{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
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

import           Prelude hiding (lookup)
import           Data.LLVM.BitCode.Parse
import           Text.LLVM.AST

import           MonadLib (Id)
import           Control.Monad (guard)
import           Lens.Micro hiding (ix)
import           Lens.Micro.TH
import qualified Control.Exception as X
import qualified Data.Map.Strict as Map

import           Data.LLVM.BitCode.IR.Metadata.Applicative
import           Data.LLVM.BitCode.IR.Metadata.Lookup

-- ** LookupMd

type LookupMd f = Lookup f Int PValMd

-- ** MetadataTable

-- | A metadata table where the mapped values are computed in the monad m.
data MetadataTable' a = MetadataTable
  { _mtEntries   :: MdTable' a
  , _mtNextNode  :: !Int
  , _mtNodes     :: Map.Map Int (Bool, Bool, Int)
                   -- ^ The entries in the map are: is the entry function local,
                   -- is the entry distinct, and the implicit id for the node.
  }

makeLenses ''MetadataTable'

-- | We only store @PValMd@ in the table. @Typed PValue@s can be recovered
-- through application of the function @Typed (PrimType Metadata)@.
type MetadataTable    = MetadataTable' PValMd
type MetadataTableF f = MetadataTable' (f PValMd)

emptyMetadataTable' :: Int -- ^ globals seen so far
                    -> MdTable' a
                    -> MetadataTable' a
emptyMetadataTable' globals es = MetadataTable
  { _mtEntries   = es
  , _mtNextNode  = globals
  , _mtNodes     = Map.empty
  }

addMetadataType :: PValMd -> Typed PValue
addMetadataType = Typed (PrimType Metadata) . ValMd

addMetadataA :: Functor f => f PValMd  -> MetadataTableF f -> (Int, MetadataTableF f)
addMetadataA val mt = (ix', mt & mtEntries .~ es')
  where (ix', es') = addValue' val (mt ^. mtEntries)

addMetadata :: Applicative f => PValMd -> MetadataTableF f -> (Int, MetadataTableF f)
addMetadata val = addMetadataA (pure val)

addMdValue :: Functor f => f (Typed PValue) -> MetadataTableF f -> MetadataTableF f
addMdValue tv mt = mt & mtEntries %~ addValue (ValMdValue <$> tv)

addString :: Applicative m => m String -> MetadataTableF m -> MetadataTableF m
addString str pm =
  pm &  mtEntries
     %~ addValue (ValMdString <$> str)

addStrings :: Applicative m
           => [m String]
           -> MetadataTableF m
           -> MetadataTableF m
addStrings strs mt = foldl (flip addString) mt strs

nameNode :: Applicative m
         => Bool -> Bool -> Int -> MetadataTableF m -> MetadataTableF m
nameNode fnLocal isDistinct ix mt =
  mt & mtNextNode %~ (+1) -- Increment node count
     & mtNodes    %~ Map.insert ix (fnLocal, isDistinct, mt ^. mtNextNode)

-- | Given an applicative value and a function converting it into a PValMd,
-- add it to the metadata table and increment the name indices
addNameNode :: Applicative f
            => f a
            -> (a -> PValMd)
            -> Bool -- ^ Function local?
            -> Bool -- ^ Distinct?
            -> MetadataTableF f
            -> MetadataTableF f
addNameNode v g fnLocal isDistinct mt = nameNode fnLocal isDistinct ix mt'
  where (ix, mt') = addMetadataA (g <$> v) mt

addLoc :: Applicative f
       => Bool -> f PDebugLoc -> MetadataTableF f -> MetadataTableF f
addLoc isDistinct loc = addNameNode loc ValMdLoc False isDistinct

addDebugInfo :: Applicative f
             => Bool -> f (DebugInfo' Int) -> MetadataTableF f -> MetadataTableF f
addDebugInfo isDistinct di = addNameNode di ValMdDebugInfo False isDistinct

-- | Add a new node, that might be distinct.
addNode :: Applicative f
        => Bool -> f [Maybe PValMd] -> MetadataTableF f -> MetadataTableF f
addNode isDistinct vals = addNameNode vals ValMdNode False isDistinct

addOldNode :: Applicative f
           => Bool -> f [Typed PValue] -> MetadataTableF f -> MetadataTableF f
addOldNode fnLocal vals = addNameNode vals (ValMdNode . map (Just . ValMdValue)) fnLocal False

-- *** Forward references

-- | Either (1) find a value in the 'mtNodes' and return its ID,
--   or use a forward reference to the value.
mdForwardRef :: (Applicative f)
             => MetadataTableF (LookupMd f)
             -> Int
             -> LookupMd f PValMd
mdForwardRef mt ix =
  case Map.lookup ix (mt ^. mtNodes) of
    Just x  -> pure $ thd x
    Nothing -> lookup ix
  where thd (_, _, r) = ValMdRef r -- "third"

-- | The same as 'mdForwardRef', but it doesn't wrap the value in a 'ValMdRef'
mdNodeRef :: Applicative f => [String] -> MetadataTableF (LookupMd f) -> Int -> LookupMd f Int
mdNodeRef cxt mt ix =
  case Map.lookup ix (mt ^. mtNodes) of
    Just x  -> pure $ thd x
    Nothing -> flip fmap (lookup ix) $
      \case
        ValMdRef i -> i
        _          -> X.throw (BadValueRef cxt ix) -- TODO: better error messages
  where thd (_, _, z) = z

mdForwardRefOrNull :: (Applicative f)
                   => MetadataTableF (LookupMd f)
                   -> Int
                   -> Maybe (LookupMd f PValMd)
mdForwardRefOrNull mt ix | ix > 0    = Just $ mdForwardRef mt (ix - 1)
                         | otherwise = Nothing

-- | This version is useful in 'Compose'd blocks
mdForwardRefOrNull' :: (Applicative f)
                    => MetadataTableF (LookupMd f)
                    -> Int
                    -> LookupMd f (Maybe PValMd)
mdForwardRefOrNull' mt = commuteMaybe . mdForwardRefOrNull mt

mdString :: Applicative f
         => [String]
         -> MetadataTableF (LookupMd f)
         -> Int
         -> LookupMd f String
mdString cxt mt ix =
  case mdStringOrNull cxt mt ix of
    Just str -> str
    Nothing  -> X.throw (NotAString cxt ix)

mdStringOrNull :: Applicative f
               => [String]
               -> MetadataTableF (LookupMd f)
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
                -> MetadataTableF (LookupMd f)
                -> Int
                -> LookupMd f (Maybe String)
mdStringOrNull' cxt mt = commuteMaybe . mdStringOrNull cxt mt

mkMdRefTable :: MetadataTable -> MdRefTable
mkMdRefTable mt = Map.mapMaybe step (mt ^. mtNodes)
  where step (fnLocal, _, ix) = do
          guard (not fnLocal)
          return ix

-- ** PartialMetadata

type PKindMd               = Int
type InstrMdAttachments    = Map.Map Int [(KindMd, PValMd)]
type InstrMdAttachmentsF f = Map.Map Int [(KindMd, f PValMd)]
type PFnMdAttachments      = Map.Map PKindMd PValMd
type PFnMdAttachmentsF   f = Map.Map PKindMd (f PValMd)
type PGlobalAttachmentsF f = Map.Map Int (Map.Map KindMd (f PValMd))
type PGlobalAttachments    = Map.Map Int (Map.Map KindMd PValMd)

-- | The fields wrapped in a @m@ are the ones that use forward references while
-- they're being parsed.
data PartialMetadata f = PartialMetadata
  { _pmEntries          :: MetadataTableF      f
  , _pmNamedEntries     :: Map.Map String      (f [Int])
  , _pmGlobalAttachments:: PGlobalAttachmentsF f
  , _pmNextName         :: Maybe String
  , _pmInstrAttachments :: InstrMdAttachmentsF f
  , _pmFnAttachments    :: PFnMdAttachmentsF   f
  }

makeLenses ''PartialMetadata

emptyPartialMetadata :: Functor f
                     => Int {- ^ globals seen so far -}
                     -> MdTableF f
                     -> PartialMetadata f
emptyPartialMetadata globals es = PartialMetadata
  { _pmEntries           = emptyMetadataTable' globals es
  , _pmNamedEntries      = Map.empty
  , _pmNextName          = Nothing
  , _pmInstrAttachments  = Map.empty
  , _pmFnAttachments     = Map.empty
  , _pmGlobalAttachments = Map.empty
  }

addGlobalAttachmentsA :: Applicative f
                      => Int                       -- ^ ID of the global to attach to
                      -> Map.Map KindMd (f PValMd) -- ^ metadata references to attach
                      -> PartialMetadata f
                      -> PartialMetadata f
addGlobalAttachmentsA ix mds pm =
  pm & pmGlobalAttachments %~ Map.insert ix mds

setNextName :: String -> PartialMetadata m -> PartialMetadata m
setNextName name = pmNextName ?~ name

-- left-biased union, since the parser overwrites metadata as it encounters it
addFnAttachment :: PFnMdAttachmentsF f -> PartialMetadata f -> PartialMetadata f
addFnAttachment att = pmFnAttachments %~ Map.union att

addInstrAttachment :: Applicative f
                   => Int
                   -> [(KindMd, f PValMd)]
                   -> PartialMetadata f
                   -> PartialMetadata f
addInstrAttachment instr md = pmInstrAttachments %~ Map.insert instr md

nameMetadataA :: Applicative f
              => f [Int] -> PartialMetadata f -> Parse (PartialMetadata f)
nameMetadataA val pm = case pm ^. pmNextName  of
  Just name ->
    return $! pm & pmNextName     .~ Nothing
                 & pmNamedEntries %~ Map.insert name val
  Nothing -> fail "Expected a metadata name"
