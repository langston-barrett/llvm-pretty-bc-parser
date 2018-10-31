{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

{-|
Module      : Data.LLVM.BitCode.IR.Metadata.Finalize
Description : Finalize parsed metadata blocks
Copyright   : (c) Galois, Inc 2018
License     : BSD-3
Maintainer  : atomb@galois.com
Stability   : experimental

NB: This happens for every metadata block, immediately after parsing.
Resolution happens after all metadata blocks have been resolved.

-}

module Data.LLVM.BitCode.IR.Metadata.Finalize where

import           Control.Lens (makeLenses)
import           Data.Either (partitionEithers)
import           Data.Maybe (mapMaybe)
import           Control.Arrow ((>>>))
import           Control.Lens hiding (ix)
import qualified Data.Map as Map
import           Data.Map (Map)

import           Data.LLVM.BitCode.Parse
import           Text.LLVM.AST
import           Text.LLVM.Labels (relabel)

import           Data.LLVM.BitCode.IR.Metadata.Table

-- ** Finalizing names

data PartialUnnamedMd' a = PartialUnnamedMd
  { _pumIndex    :: Int
  , _pumValues   :: a
  , _pumDistinct :: Bool
  }

makeLenses ''PartialUnnamedMd'

type PartialUnnamedMd    = PartialUnnamedMd' PValMd
type PartialUnnamedMdF f = PartialUnnamedMd' (f PValMd)

finalizePartialUnnamedMd :: PartialUnnamedMd -> Parse UnnamedMd
finalizePartialUnnamedMd pum = mkUnnamedMd <$> finalizePValMd (pum ^. pumValues)
  where mkUnnamedMd v = UnnamedMd
          -- Take the results that were resolved and add them to the state.
          { umIndex    = pum ^. pumIndex
          , umValues   = v
          , umDistinct = pum ^. pumDistinct
          }

finalizePValMd :: PValMd -> Parse ValMd
finalizePValMd = relabel (const requireBbEntryName)

finalizePValMd' :: ValueSymtab -> PValMd -> Maybe ValMd
finalizePValMd' symtab = relabel (const (bbEntryName' symtab))

namedEntries :: Applicative f => PartialMetadata f -> [f NamedMd]
namedEntries =
  (^. pmNamedEntries)                  -- Map String [f Int]
  >>> Map.map sequenceA                -- Map String (f [Int])
  >>> Map.toList                       -- [(String, f [Int])]
  >>> map (\(s, i) -> NamedMd s <$> i) -- [f NamedMd]

-- | Partition unnamed entries into global and function local unnamed entries.
unnamedEntries :: forall f. (Applicative f)
               => PartialMetadata f
               -> ([PartialUnnamedMdF f], [PartialUnnamedMdF f])
unnamedEntries pm =
  partitionEithers . mapMaybe (resolveNode (valueEntries $ pm ^. pmEntries . mtEntries)) $
    Map.toList $ pm ^. pmEntries . mtNodes
  where
    -- TODO: is this silently eating errors with metadata that's not in the
    -- value table (by passing along the 'Nothing' from the Map lookup)?
    resolveNode :: Map Int (f PValMd)           -- ^ mtEntries
                -> (Int, (Bool, Bool, Int))     -- ^ mtNodes
                -> Maybe (Either (PartialUnnamedMdF f) (PartialUnnamedMdF f))
    resolveNode entries (ref, (fnLocal, isDistinct, ix)) =
      flip fmap (Map.lookup ref entries) $ \val ->
        (if fnLocal then Left else Right) (PartialUnnamedMd ix val isDistinct)
