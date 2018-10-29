{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

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

import           Data.Either (partitionEithers)
import           Data.Maybe (mapMaybe)
import           Control.Arrow ((>>>))
import           Lens.Micro hiding (ix)
import qualified Data.Map as Map
import           Data.Map (Map)

import           Data.LLVM.BitCode.Parse
import           Text.LLVM.AST
import           Text.LLVM.Labels (relabel)

import           Data.LLVM.BitCode.IR.Metadata.Applicative (seqMap)
import           Data.LLVM.BitCode.IR.Metadata.Table

-- ** Finalizing names

data PartialUnnamedMd = PartialUnnamedMd
  { pumIndex    :: Int
  , pumValues   :: PValMd
  , pumDistinct :: Bool
  } deriving (Show)

finalizePartialUnnamedMd :: PartialUnnamedMd -> Parse UnnamedMd
finalizePartialUnnamedMd pum = mkUnnamedMd `fmap` finalizePValMd (pumValues pum)
  where
  mkUnnamedMd v = UnnamedMd

  -- Take the results that were resolved and add them to the state.
    { umIndex  = pumIndex pum
    , umValues = v
    , umDistinct = pumDistinct pum
    }

finalizePValMd :: PValMd -> Parse ValMd
finalizePValMd = relabel (const requireBbEntryName)

namedEntries :: Applicative f => PartialMetadata f -> f [NamedMd]
namedEntries =
  (^. pmNamedEntries)                       -- Map String (m [Int])
  >>> Map.toList                            -- [(String, f [Int])]
  >>> traverse (\(s, i) -> NamedMd s <$> i) -- f [NamedMd]

-- | Partition unnamed entries into global and function local unnamed entries.
unnamedEntries :: forall f. (Applicative f)
               => PartialMetadata f
               -> f ([PartialUnnamedMd], [PartialUnnamedMd])
unnamedEntries pm =
  (\entries -> partitionEithers . mapMaybe (resolveNode entries) . Map.toList)
  <$> seqMap (valueEntries $ pm ^. pmEntries . mtEntries)
  <*> pure (pm ^. pmEntries . mtNodes)
  where
    -- TODO: is this silently eating errors with metadata that's not in the
    -- value table (by passing along the 'Nothing' from the Map lookup)?
    --
    -- NB: the bind (=<<) happens in 'Maybe'.
    resolveNode :: Map Int (Typed PValue)   -- ^ mtEntries
                -> (Int, (Bool, Bool, Int)) -- ^ mtNodes
                -> Maybe (Either PartialUnnamedMd PartialUnnamedMd)
    resolveNode entries (ref, (fnLocal, isDistinct, ix)) =
      (if fnLocal then Left else Right) <$>
        (mkPartialUnnamedMd ix isDistinct =<< Map.lookup ref entries)

    mkPartialUnnamedMd :: Int -> Bool -> Typed PValue -> Maybe PartialUnnamedMd
    mkPartialUnnamedMd ix d =
      \case
        Typed{ typedValue = ValMd v } ->
          Just PartialUnnamedMd
            { pumIndex    = ix
            , pumValues   = v
            , pumDistinct = d
            }
        _ -> Nothing
