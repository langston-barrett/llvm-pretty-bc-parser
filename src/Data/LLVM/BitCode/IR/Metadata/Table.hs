{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-|
Module      : Data.LLVM.BitCode.IR.Metadata.Table
Description : The parsing state for metadata blocks
LookupMd fopyright   : (c) Galois, Inc 2018
License     : BSD-3
Maintainer  : atomb@galois.com
Stability   : experimental

This module 'MetadataTable' and 'PartialMetadata', which are used
internally while processing a metadata block.
-}

module Data.LLVM.BitCode.IR.Metadata.Table where

import           Data.LLVM.BitCode.Parse
import           Text.LLVM.AST

import           Control.Monad (guard)
import           Lens.Micro hiding (ix)
import           Lens.Micro.TH
import qualified Control.Exception as X
import qualified Data.Map as Map

import           Debug.Trace

import           Data.LLVM.BitCode.IR.Metadata.Applicative
import           Data.LLVM.BitCode.IR.Metadata.Lookup


-- ** MetadataTable

-- | A metadata table where the mapped values are computed in the monad m.
data MetadataTable' a b = MetadataTable
  { _mtEntries   :: MdTable' a
  , _mtNextNode  :: !Int
  , _mtNodes     :: Map.Map Int b
                   -- ^ The entries in the map are: is the entry function local,
                   -- is the entry distinct, and the implicit id for the node.
  }

makeLenses ''MetadataTable'

type MetadataTable    = MetadataTable' (Typed PValue) (Bool, Bool, Int)
type MetadataTableM m = MetadataTable' (m (Typed PValue)) (m (Bool, Bool, Int))

emptyMetadataTable' :: Int -- ^ globals seen so far
                    -> MdTable' a
                    -> MetadataTable' a b
emptyMetadataTable' globals es = MetadataTable
  { _mtEntries   = es
  , _mtNextNode  = globals
  , _mtNodes     = Map.empty
  }

metadata :: PValMd -> Typed PValue
metadata  = Typed (PrimType Metadata) . ValMd

addMetadataA :: Functor f => f PValMd  -> MetadataTableM f -> (Int, MetadataTableM f)
addMetadataA val mt = (ix', mt & mtEntries .~ es')
  where (ix', es') = addValue' (metadata <$> val) (mt ^. mtEntries)

addMetadata :: Applicative f => PValMd -> MetadataTableM f -> (Int, MetadataTableM f)
addMetadata val = addMetadataA (pure val)

addMdValue :: Functor f => f (Typed PValue) -> MetadataTableM f -> MetadataTableM f
addMdValue tv mt = mt & mtEntries %~ addValue (typeIt <$> tv)
  where
  -- explicitly make a metadata value out of a normal value
  typeIt v = Typed { typedType  = PrimType Metadata
                   , typedValue = ValMd (ValMdValue v)
                   }

addString :: Applicative m => m String -> MetadataTableM m -> MetadataTableM m
addString str pm =
  pm &  mtEntries
     %~ addValue (metadata . ValMdString <$> str)

addStrings :: Applicative m
           => [m String]
           -> MetadataTableM m
           -> MetadataTableM m
addStrings strs mt = foldl (flip addString) mt strs

nameNodeA :: Applicative m
          => m Bool -- ^ Is the node function-local?
          -> m Bool -- ^ Is the node "distinct"?
          -> Int    -- ^ Index to insert at
          -> MetadataTableM m
          -> MetadataTableM m
nameNodeA fnLocal isDistinct ix mt =
  mt & mtNextNode %~ (+1) -- Increment node count
     & mtNodes    %~ Map.insert ix (tupleA3 (fnLocal, isDistinct, pure $ mt ^. mtNextNode))

-- | See 'nameNodeA'.
nameNode :: Applicative m
         => Bool -> Bool -> Int -> MetadataTableM m -> MetadataTableM m
nameNode fnLocal isDistinct = nameNodeA (pure fnLocal) (pure isDistinct)

-- | Given an applicative value and a function converting it into a PValMd,
-- add it to the metadata table and increment the name indices
addNameNode :: Applicative f
            => f a
            -> (a -> PValMd)
            -> Bool -- ^ Function local?
            -> Bool -- ^ Distinct?
            -> MetadataTableM f
            -> MetadataTableM f
addNameNode v g fnLocal isDistinct mt = nameNode fnLocal isDistinct ix mt'
  where (ix, mt') = addMetadataA (g <$> v) mt

addLoc :: Applicative f
       => Bool -> f PDebugLoc -> MetadataTableM f -> MetadataTableM f
addLoc isDistinct loc = addNameNode loc ValMdLoc False isDistinct

addDebugInfo :: Applicative f
             => Bool -> f (DebugInfo' Int) -> MetadataTableM f -> MetadataTableM f
addDebugInfo isDistinct di = addNameNode di ValMdDebugInfo False isDistinct

-- | Add a new node, that might be distinct.
addNode :: Applicative f
        => Bool -> f [Maybe PValMd] -> MetadataTableM f -> MetadataTableM f
addNode isDistinct vals = addNameNode vals ValMdNode False isDistinct

addOldNode :: Applicative f
           => Bool -> f [Typed PValue] -> MetadataTableM f -> MetadataTableM f
addOldNode fnLocal vals = addNameNode vals (ValMdNode . map (Just . ValMdValue)) fnLocal False

-- | Either (1) find a value in the 'mtNodes' and return its TODO,
--   or use a forward reference to the value.
mdForwardRef :: (Applicative f)
             => MetadataTableM (LookupMd f)
             -> Int
             -> LookupMd f PValMd
mdForwardRef mt ix =
  case Map.lookup ix (mt ^. mtNodes) of
    Just x  -> thd <$> x
    Nothing ->
      withLookup ix $
        \case
          Typed { typedValue = ValMd md } -> md
          tv                              -> ValMdValue tv
  where thd (_, _, r) = ValMdRef r -- "third"

mdForwardRefOrNull :: (Applicative f)
                   => MetadataTableM (LookupMd f)
                   -> Int
                   -> Maybe (LookupMd f PValMd)
mdForwardRefOrNull mt ix | ix > 0    = Just $ mdForwardRef mt (ix - 1)
                         | otherwise = Nothing

-- | This version is useful in 'Compose'd blocks
mdForwardRefOrNull' :: (Applicative f)
                    => MetadataTableM (LookupMd f)
                    -> Int
                    -> LookupMd f (Maybe PValMd)
mdForwardRefOrNull' mt = commuteMaybe . mdForwardRefOrNull mt

mdNodeRef :: Functor f => [String] -> MetadataTableM f -> Int -> f Int
mdNodeRef cxt mt ix =
  case Map.lookup ix (mt ^. mtNodes) of
    Just x  -> fmap thd x
    Nothing -> X.throw (BadValueRef cxt ix) -- TODO: better error messages
  where thd (_, _, z) = z

mdString :: Applicative f
         => [String]
         -> MetadataTableM (LookupMd f)
         -> Int
         -> LookupMd f String
mdString cxt mt ix =
  case mdStringOrNull cxt mt ix of
    Just str -> str
    Nothing  -> X.throw (BadValueRef cxt ix)

mdStringOrNull :: Applicative f
               => [String]
               -> MetadataTableM (LookupMd f)
               -> Int
               -> Maybe (LookupMd f String)
mdStringOrNull cxt mt ix =
  case mdForwardRefOrNull mt ix of
      Just y  -> Just $ flip fmap y $
        \case
          (ValMdString str) -> str
          _                 -> X.throw (BadTypeRef cxt ix)
      Nothing -> Nothing

-- | This version is useful in 'Compose'd blocks
mdStringOrNull' :: Applicative f
                => [String]
                -> MetadataTableM (LookupMd f)
                -> Int
                -> LookupMd f (Maybe String)
mdStringOrNull' cxt mt = commuteMaybe . mdStringOrNull cxt mt

mkMdRefTable :: MetadataTable -> MdRefTable
mkMdRefTable mt = Map.mapMaybe step (mt ^. mtNodes)
  where step (fnLocal, _, ix) = do
          guard (not fnLocal)
          return ix

-- ** LookupMd

type LookupMd f = Lookup f Int (Typed PValue)

-- ** PartialMetadata

type PKindMd               = Int
type InstrMdAttachments    = Map.Map Int [(KindMd,PValMd)]
type PFnMdAttachments      = Map.Map PKindMd PValMd
type PGlobalAttachments' v = Map.Map Symbol v
type PGlobalAttachments    = Map.Map Symbol (Map.Map KindMd PValMd)

-- | The fields wrapped in a @m@ are the ones that use forward references while
-- they're being parsed.
data PartialMetadata m = PartialMetadata
  { _pmEntries          :: MetadataTableM       m
  , _pmNamedEntries     :: Map.Map String      (m [Int])
  , _pmGlobalAttachments:: PGlobalAttachments' (m (Map.Map KindMd PValMd))
  , _pmNextName         :: Maybe String
  , _pmInstrAttachments :: InstrMdAttachments
  , _pmFnAttachments    :: PFnMdAttachments
  }

makeLenses ''PartialMetadata

emptyPartialMetadata :: Functor m
                     => Int {- ^ globals seen so far -}
                     -> MdTable' (m (Typed PValue))
                     -> PartialMetadata m
emptyPartialMetadata globals es = PartialMetadata
  { _pmEntries           = emptyMetadataTable' globals es
  , _pmNamedEntries      = Map.empty
  , _pmNextName          = Nothing
  , _pmInstrAttachments  = Map.empty
  , _pmFnAttachments     = Map.empty
  , _pmGlobalAttachments = Map.empty
  }

addGlobalAttachmentsA :: Applicative m
                      => Symbol                    -- ^ name of the global to attach to
                      -> m (Map.Map KindMd PValMd) -- ^ metadata references to attach
                      -> PartialMetadata m
                      -> PartialMetadata m
addGlobalAttachmentsA sym mds pm =
  pm & pmGlobalAttachments %~ Map.insert sym mds

setNextName :: String -> PartialMetadata m -> PartialMetadata m
setNextName name = pmNextName ?~ name

-- left-biased union, since the parser overwrites metadata as it encounters it
addFnAttachment :: PFnMdAttachments -> PartialMetadata m -> PartialMetadata m
addFnAttachment att = pmFnAttachments %~ Map.union att

addInstrAttachment :: Int -> [(KindMd,PValMd)]
                   -> PartialMetadata m -> PartialMetadata m
addInstrAttachment instr md = pmInstrAttachments %~ Map.insert instr md

nameMetadataA :: Applicative m
              => m [Int] -> PartialMetadata m -> Parse (PartialMetadata m)
nameMetadataA val pm = case pm ^. pmNextName  of
  Just name ->
    return $! pm & pmNextName     .~ Nothing
                 & pmNamedEntries %~ Map.insert name val
  Nothing -> fail "Expected a metadata name"
