{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-|
Module      : Data.LLVM.BitCode.IR.Metadata.Table
Description : The parsing state for metadata blocks
Copyright   : (c) Galois, Inc 2018
License     : BSD-3
Maintainer  : atomb@galois.com
Stability   : experimental

This module 'MetadataTable' and 'PartialMetadataTable', which are used
internally while processing a metadata block.
-}

module Data.LLVM.BitCode.IR.Metadata.Table where

import Data.LLVM.BitCode.Parse
import Text.LLVM.AST
import Text.LLVM.Labels

import           Control.Monad (guard)
import qualified Control.Exception as X
--import Data.Maybe (fromMaybe)
import qualified Data.Map as Map

import Data.LLVM.BitCode.IR.Metadata.Lookup

-- ** MetadataTable

data MetadataTable = MetadataTable
  { mtEntries   :: MdTable
  , mtNextNode  :: !Int
  , mtNodes     :: Map.Map Int (Bool,Bool,Int)
                   -- ^ The entries in the map are: is the entry function local,
                   -- is the entry distinct, and the implicit id for the node.
  } deriving (Show)

emptyMetadataTable ::
  Int {- ^ globals seen so far -} ->
  MdTable -> MetadataTable
emptyMetadataTable globals es = MetadataTable
  { mtEntries   = es
  , mtNextNode  = globals
  , mtNodes     = Map.empty
  }

metadata :: PValMd -> Typed PValue
metadata  = Typed (PrimType Metadata) . ValMd


addMetadata :: PValMd  -> MetadataTable -> (Int,MetadataTable)
addMetadata val mt = (ix, mt { mtEntries = es' })
  where (ix, es') = addValue' (metadata val) (mtEntries mt)

-- addMetadata' :: Applicative f => f PValMd -> f MetadataTable -> f (Int, MetadataTable)
-- addMetadata' val mt = addMetadata <$> val <*> mt

addMdValue :: Typed PValue -> MetadataTable -> MetadataTable
addMdValue tv mt = mt { mtEntries = addValue tv' (mtEntries mt) }
  where
  -- explicitly make a metadata value out of a normal value
  tv' = Typed { typedType  = PrimType Metadata
              , typedValue = ValMd (ValMdValue tv)
              }

nameNode :: Bool -> Bool -> Int -> MetadataTable -> MetadataTable
nameNode fnLocal isDistinct ix mt = mt
  { mtNodes    = Map.insert ix (fnLocal,isDistinct,mtNextNode mt) (mtNodes mt)
  , mtNextNode = mtNextNode mt + 1
  }

addString :: String -> MetadataTable -> MetadataTable
addString str = snd . addMetadata (ValMdString str)

addStrings :: [String] -> MetadataTable -> MetadataTable
addStrings strs mt = foldl (flip addString) mt strs

addLoc :: Bool -> PDebugLoc -> MetadataTable -> MetadataTable
addLoc isDistinct loc mt = nameNode False isDistinct ix mt'
  where (ix, mt') = addMetadata (ValMdLoc loc) mt

-- addLoc :: Applicative f
--        => Bool -> f PDebugLoc -> f MetadataTable -> f MetadataTable
-- addLoc isDistinct loc mt = nameNode False isDistinct <$> ix <*> mt'
--   where (ix, mt') = addMetadata (ValMdLoc loc) mt

-- addLoc :: Bool -> PDebugLoc -> MetadataTable -> MetadataTable
-- addLoc isDistinct loc mt = nameNode False isDistinct ix mt'
--   where (ix, mt') = addMetadata (ValMdLoc loc) mt

addDebugInfo
  :: Bool
  -> DebugInfo' Int
  -> MetadataTable
  -> MetadataTable
addDebugInfo isDistinct di mt = nameNode False isDistinct ix mt'
  where
  (ix,mt') = addMetadata (ValMdDebugInfo di) mt

-- | Add a new node, that might be distinct.
addNode :: Bool -> [Maybe PValMd] -> MetadataTable -> MetadataTable
addNode isDistinct vals mt = nameNode False isDistinct ix mt'
  where (ix, mt') = addMetadata (ValMdNode vals) mt

addOldNode :: Bool -> [Typed PValue] -> MetadataTable -> MetadataTable
addOldNode fnLocal vals mt = nameNode fnLocal False ix mt'
  where (ix, mt') = addMetadata (ValMdNode [ Just (ValMdValue tv) | tv <- vals ]) mt

-- | Either (1) find a value in the 'mtNodes' and return its TODO,
--   or use a forward reference to the value.
mdForwardRef :: LookupMd m => MetadataTable -> Int -> m PValMd
mdForwardRef mt ix =
  case thd <$> Map.lookup ix (mtNodes mt) of
    Just x  -> pure x
    Nothing ->
      withLookup ix $
        \case
          Typed { typedValue = ValMd md } -> md
          tv                              -> ValMdValue tv
  where thd (_, _, r) = ValMdRef r -- "third"

mdForwardRefOrNull :: LookupMd m
                   => MetadataTable
                   -> Int
                   -> Maybe (m PValMd)
mdForwardRefOrNull mt ix | ix > 0 = Just (mdForwardRef mt (ix - 1))
                         | otherwise = Nothing

mdNodeRef :: Functor f => [String] -> f MetadataTable -> Int -> f Int
mdNodeRef cxt mt ix =
  flip fmap (Map.lookup ix <$> (mtNodes <$> mt)) $
    \case
      Just (_, _, x) -> x
      Nothing        -> X.throw (BadValueRef cxt ix)

mdString :: LookupMd m => [String] -> MetadataTable -> Int -> m String
mdString cxt mt ix =
  case mdStringOrNull cxt mt ix of
    Just str -> str
    Nothing  -> X.throw (BadValueRef cxt ix)

mdStringOrNull :: LookupMd m
               => [String]
               -> MetadataTable
               -> Int
               -> Maybe (m String)
mdStringOrNull cxt mt ix =
  case mdForwardRefOrNull mt ix of
      Just y  -> pure $ flip fmap y $
        \case
          (ValMdString str) -> str
          _                 -> X.throw (BadTypeRef cxt ix)
      Nothing -> Nothing

mkMdRefTable :: MetadataTable -> MdRefTable
mkMdRefTable mt = Map.mapMaybe step (mtNodes mt)
  where
  step (fnLocal,_,ix) = do
    guard (not fnLocal)
    return ix

-- ** LookupMd

-- | @LookupMd m a
--   = Lookup m (Typed PValue) a
--   = ReaderM m (Int -> m (Typed PValue)) a
--   = (Int -> m (Typed PValue)) -> m a@
type LookupMd m = Lookup m Int (Typed PValue)

-- ** PartialMetadata

data PartialMetadata m = PartialMetadata
  { pmEntries          :: LookupMd m => m MetadataTable
  , pmNamedEntries     :: Map.Map String [Int]
  , pmNextName         :: Maybe String
  , pmInstrAttachments :: InstrMdAttachments
  , pmFnAttachments    :: PFnMdAttachments
  , pmGlobalAttachments:: PGlobalAttachments
  }

emptyPartialMetadata :: Applicative m
                     => Int {- ^ globals seen so far -}
                     -> MdTable
                     -> PartialMetadata m
emptyPartialMetadata globals es = PartialMetadata
  { pmEntries          = pure $ emptyMetadataTable globals es
  , pmNamedEntries     = Map.empty
  , pmNextName         = Nothing
  , pmInstrAttachments = Map.empty
  , pmFnAttachments    = Map.empty
  , pmGlobalAttachments= Map.empty
  }

updateMetadataTable :: Functor f
                    => (MetadataTable -> MetadataTable)
                    -> (PartialMetadata f -> PartialMetadata f)
updateMetadataTable f pm = pm { pmEntries = f <$> pmEntries pm }

updateMetadataTableA :: Applicative f
                     => f (MetadataTable -> MetadataTable)
                     -> (PartialMetadata f -> PartialMetadata f)
updateMetadataTableA f pm = pm { pmEntries = f <*> pmEntries pm }

addGlobalAttachments ::
  Symbol {- ^ name of the global to attach to ^ -} ->
  Map.Map KindMd PValMd {- ^ metadata references to attach ^ -} ->
  (PartialMetadata m -> PartialMetadata m)
addGlobalAttachments sym mds pm =
  pm { pmGlobalAttachments = Map.insert sym mds (pmGlobalAttachments pm)
     }

setNextName :: String -> PartialMetadata m -> PartialMetadata m
setNextName name pm = pm { pmNextName = Just name }

addFnAttachment :: PFnMdAttachments -> PartialMetadata m -> PartialMetadata m
addFnAttachment att pm =
  -- left-biased union, since the parser overwrites metadata as it encounters it
  pm { pmFnAttachments = Map.union att (pmFnAttachments pm) }

addInstrAttachment :: Int -> [(KindMd,PValMd)]
                   -> PartialMetadata m -> PartialMetadata m
addInstrAttachment instr md pm =
  pm { pmInstrAttachments = Map.insert instr md (pmInstrAttachments pm) }

nameMetadata :: [Int] -> PartialMetadata m -> Parse (PartialMetadata m)
nameMetadata val pm = case pmNextName pm of
  Just name -> return $! pm
    { pmNextName     = Nothing
    , pmNamedEntries = Map.insert name val (pmNamedEntries pm)
    }
  Nothing -> fail "Expected a metadata name"

namedEntries :: PartialMetadata m -> [NamedMd]
namedEntries  = map (uncurry NamedMd)
              . Map.toList
              . pmNamedEntries

data PartialUnnamedMd = PartialUnnamedMd
  { pumIndex    :: Int
  , pumValues   :: PValMd
  , pumDistinct :: Bool
  } deriving (Show)

finalizePartialUnnamedMd :: PartialUnnamedMd -> Parse UnnamedMd
finalizePartialUnnamedMd pum = mkUnnamedMd `fmap` finalizePValMd (pumValues pum)
  where
  mkUnnamedMd v = UnnamedMd
    { umIndex  = pumIndex pum
    , umValues = v
    , umDistinct = pumDistinct pum
    }

finalizePValMd :: PValMd -> Parse ValMd
finalizePValMd = relabel (const requireBbEntryName)

-- | Partition unnamed entries into global and function local unnamed entries.
{-
unnamedEntries :: PartialMetadata m -> ([PartialUnnamedMd],[PartialUnnamedMd])
unnamedEntries pm = foldl resolveNode ([],[]) (Map.toList (mtNodes mt))
  where
  mt = pmEntries pm

  resolveNode (gs,fs) (ref,(fnLocal,d,ix)) = case lookupNode ref d ix of
    Just pum | fnLocal   -> (gs,pum:fs)
             | otherwise -> (pum:gs,fs)

    -- TODO: is this silently eating errors with metadata that's not in the
    -- value table?
    Nothing              -> (gs,fs)

  lookupNode ref d ix = do
    Typed { typedValue = ValMd v } <- lookupValueTableAbs ref (mtEntries mt)
    return PartialUnnamedMd
      { pumIndex  = ix
      , pumValues = v
      , pumDistinct = d
      }
-}

type InstrMdAttachments = Map.Map Int [(KindMd,PValMd)]

type PKindMd = Int
type PFnMdAttachments = Map.Map PKindMd PValMd
type PGlobalAttachments = Map.Map Symbol (Map.Map KindMd PValMd)

type ParsedMetadata =
  ( [NamedMd]
  , ([PartialUnnamedMd],[PartialUnnamedMd])
  , InstrMdAttachments
  , PFnMdAttachments
  , PGlobalAttachments
  )

{-
parsedMetadata :: PartialMetadata m -> ParsedMetadata
parsedMetadata pm =
  ( namedEntries pm
  , unnamedEntries pm
  , pmInstrAttachments pm
  , pmFnAttachments pm
  , pmGlobalAttachments pm
  )
-}
