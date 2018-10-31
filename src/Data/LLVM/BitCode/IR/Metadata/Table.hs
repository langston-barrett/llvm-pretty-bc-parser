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

import           Prelude hiding (lookup)
import           Data.LLVM.BitCode.Parse
import           Text.LLVM.AST

import           MonadLib (Id)
import           Control.Monad (guard)
import           Control.Lens hiding (ix)
import qualified Control.Exception as X
import qualified Data.Map as Map

import           Data.LLVM.BitCode.IR.Metadata.Applicative
import           Data.LLVM.BitCode.IR.Metadata.Lookup

-- ** LookupMd

type LookupMd f = Lookup f Int PValMd

-- ** MetadataTable

-- | A metadata table where the mapped values are computed in the monad m.
data MetadataTable' f = MetadataTable
  { _mtEntries   :: MdTable' f
  , _mtNextNode  :: !Int
  , _mtNodes     :: Map.Map Int (Bool, Bool, Int)
                   -- ^ The entries in the map are: is the entry function local,
                   -- is the entry distinct, and the implicit id for the node.
  }

makeLenses ''MetadataTable'

-- | We only store @PValMd@ in the table. @Typed PValue@s can be recovered
-- through application of the function @Typed (PrimType Metadata)@.
type MetadataTable    = MetadataTable' Id

emptyMetadataTable' :: Int -- ^ globals seen so far
                    -> MdTable' a
                    -> MetadataTable' a
emptyMetadataTable' globals es = MetadataTable
  { _mtEntries   = es
  , _mtNextNode  = globals
  , _mtNodes     = Map.empty
  }

-- metadata :: PValMd -> Typed PValue
-- metadata  = Typed (PrimType Metadata) . ValMd

addMetadataA :: Functor f => f PValMd  -> MetadataTable' f -> (Int, MetadataTable' f)
addMetadataA val mt = (ix', mt & mtEntries .~ es')
  where (ix', es') = addValue' val (mt ^. mtEntries)

addMetadata :: Applicative f => PValMd -> MetadataTable' f -> (Int, MetadataTable' f)
addMetadata val = addMetadataA (pure val)

addMdValue :: Functor f => f (Typed PValue) -> MetadataTable' f -> MetadataTable' f
addMdValue tv mt = mt & mtEntries %~ addValue (ValMdValue <$> tv)

addString :: Applicative m => m String -> MetadataTable' m -> MetadataTable' m
addString str pm =
  pm &  mtEntries
     %~ addValue (ValMdString <$> str)

addStrings :: Applicative m
           => [m String]
           -> MetadataTable' m
           -> MetadataTable' m
addStrings strs mt = foldl (flip addString) mt strs

nameNode :: Applicative m
         => Bool -> Bool -> Int -> MetadataTable' m -> MetadataTable' m
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
            -> MetadataTable' f
            -> MetadataTable' f
addNameNode v g fnLocal isDistinct mt = nameNode fnLocal isDistinct ix mt'
  where (ix, mt') = addMetadataA (g <$> v) mt

addLoc :: Applicative f
       => Bool -> f PDebugLoc -> MetadataTable' f -> MetadataTable' f
addLoc isDistinct loc = addNameNode loc ValMdLoc False isDistinct

addDebugInfo :: Applicative f
             => Bool -> f (DebugInfo' Int) -> MetadataTable' f -> MetadataTable' f
addDebugInfo isDistinct di = addNameNode di ValMdDebugInfo False isDistinct

-- | Add a new node, that might be distinct.
addNode :: Applicative f
        => Bool -> f [Maybe PValMd] -> MetadataTable' f -> MetadataTable' f
addNode isDistinct vals = addNameNode vals ValMdNode False isDistinct

addOldNode :: Applicative f
           => Bool -> f [Typed PValue] -> MetadataTable' f -> MetadataTable' f
addOldNode fnLocal vals = addNameNode vals (ValMdNode . map (Just . ValMdValue)) fnLocal False

-- *** Forward references

-- | Either (1) find a value in the 'mtNodes' and return its TODO,
--   or use a forward reference to the value.
mdForwardRef :: (Applicative f)
             => MetadataTable' (LookupMd f)
             -> Int
             -> LookupMd f PValMd
mdForwardRef mt ix =
  case Map.lookup ix (mt ^. mtNodes) of
    Just x  -> pure $ thd x
    Nothing -> lookup ix
  where thd (_, _, r) = ValMdRef r -- "third"

mdForwardRefOrNull :: (Applicative f)
                   => MetadataTable' (LookupMd f)
                   -> Int
                   -> Maybe (LookupMd f PValMd)
mdForwardRefOrNull mt ix | ix > 0    = Just $ mdForwardRef mt (ix - 1)
                         | otherwise = Nothing

-- | This version is useful in 'Compose'd blocks
mdForwardRefOrNull' :: (Applicative f)
                    => MetadataTable' (LookupMd f)
                    -> Int
                    -> LookupMd f (Maybe PValMd)
mdForwardRefOrNull' mt = commuteMaybe . mdForwardRefOrNull mt

mdNodeRef :: Applicative f => [String] -> MetadataTable' f -> Int -> f Int
mdNodeRef cxt mt ix =
  case Map.lookup ix (mt ^. mtNodes) of
    Just x  -> pure $ thd x
    Nothing -> X.throw (BadValueRef cxt ix) -- TODO: better error messages
  where thd (_, _, z) = z

mdString :: Applicative f
         => [String]
         -> MetadataTable' (LookupMd f)
         -> Int
         -> LookupMd f String
mdString cxt mt ix =
  case mdStringOrNull cxt mt ix of
    Just str -> str
    Nothing  -> X.throw (BadValueRef cxt ix)

mdStringOrNull :: Applicative f
               => [String]
               -> MetadataTable' (LookupMd f)
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
                -> MetadataTable' (LookupMd f)
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
type InstrMdAttachments    = Map.Map Int [(KindMd,PValMd)]
type PFnMdAttachments      = Map.Map PKindMd PValMd
type PGlobalAttachmentsF f = Map.Map Symbol (Map.Map KindMd (f PValMd))
type PGlobalAttachments    = Map.Map Symbol (Map.Map KindMd PValMd)

-- | The fields wrapped in a @m@ are the ones that use forward references while
-- they're being parsed.
data PartialMetadata f = PartialMetadata
  { _pmEntries          :: MetadataTable'      f
  , _pmNamedEntries     :: Map.Map String      [f Int]
  , _pmGlobalAttachments:: PGlobalAttachmentsF f
  , _pmNextName         :: Maybe String
  , _pmInstrAttachments :: InstrMdAttachments
  , _pmFnAttachments    :: PFnMdAttachments
  }

makeLenses ''PartialMetadata

emptyPartialMetadata :: Functor m
                     => Int {- ^ globals seen so far -}
                     -> MdTable' m
                     -> PartialMetadata m
emptyPartialMetadata globals es = PartialMetadata
  { _pmEntries           = emptyMetadataTable' globals es
  , _pmNamedEntries      = Map.empty
  , _pmNextName          = Nothing
  , _pmInstrAttachments  = Map.empty
  , _pmFnAttachments     = Map.empty
  , _pmGlobalAttachments = Map.empty
  }

addGlobalAttachmentsA :: Applicative f
                      => Symbol                    -- ^ name of the global to attach to
                      -> Map.Map KindMd (f PValMd) -- ^ metadata references to attach
                      -> PartialMetadata f
                      -> PartialMetadata f
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

nameMetadataA :: Applicative f
              => [f Int] -> PartialMetadata f -> Parse (PartialMetadata f)
nameMetadataA val pm = case pm ^. pmNextName  of
  Just name ->
    return $! pm & pmNextName     .~ Nothing
                 & pmNamedEntries %~ Map.insert name val
  Nothing -> fail "Expected a metadata name"
