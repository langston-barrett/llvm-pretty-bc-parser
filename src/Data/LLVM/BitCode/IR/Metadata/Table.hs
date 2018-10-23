{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
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

import           Control.Arrow ((>>>))
import           Control.Monad (guard)
import qualified Control.Exception as X
import qualified Data.Map as Map

import Data.LLVM.BitCode.IR.Metadata.Lookup
import Data.LLVM.BitCode.IR.Metadata.Applicative

-- ** MetadataTable

-- | A metadata table where the mapped values are computed in the monad m.
data MetadataTable' a b = MetadataTable
  { mtEntries   :: MdTable' a
  , mtNextNode  :: !Int
  , mtNodes     :: Map.Map Int b
                   -- ^ The entries in the map are: is the entry function local,
                   -- is the entry distinct, and the implicit id for the node.
  }

type MetadataTable    = MetadataTable' (Typed PValue) (Bool, Bool, Int)
type MetadataTableM m = MetadataTable' (m (Typed PValue)) (m (Bool, Bool, Int))

emptyMetadataTable' :: Int -- ^ globals seen so far
                    -> MdTable' a
                    -> MetadataTable' a b
emptyMetadataTable' globals es = MetadataTable
  { mtEntries   = es
  , mtNextNode  = globals
  , mtNodes     = Map.empty
  }

metadata :: PValMd -> Typed PValue
metadata  = Typed (PrimType Metadata) . ValMd

addMetadata :: Functor f => f PValMd  -> MetadataTableM f -> (Int, MetadataTableM f)
addMetadata val mt = (ix, mt { mtEntries = es' })
  where (ix, es') = addValue' (metadata <$> val) (mtEntries mt)

-- addMetadata' :: Applicative f => f PValMd -> f MetadataTableM m -> f (Int, MetadataTable)
-- addMetadata' val mt = addMetadata <$> val <*> mt

addMdValue :: Functor f => f (Typed PValue) -> MetadataTableM f -> MetadataTableM f
addMdValue tv mt = mt { mtEntries = addValue (tv' <$> tv) (mtEntries mt) }
  where
  -- explicitly make a metadata value out of a normal value
  tv' tv = Typed { typedType  = PrimType Metadata
                 , typedValue = ValMd (ValMdValue tv)
                 }

nameNodeA :: Applicative m
          => m Bool -- ^ Is the node function-local?
          -> m Bool -- ^ Is the node "distinct"?
          -> Int  -- ^ Index to insert at
          -> MetadataTableM m
          -> MetadataTableM m
nameNodeA fnLocal isDistinct ix mt = mt
  { mtNodes    = Map.insert ix (tupleA3 (fnLocal, isDistinct, pure $ mtNextNode mt)) (mtNodes mt)
  , mtNextNode = mtNextNode mt + 1
  }

nameNode :: Applicative m
         => Bool -- ^ Is the node function-local?
         -> Bool -- ^ Is the node "distinct"?
         -> Int  -- ^ Index to insert at
         -> MetadataTableM m
         -> MetadataTableM m
nameNode fnLocal isDistinct = nameNodeA (pure fnLocal) (pure isDistinct)

addStringA :: Applicative m => m String -> MetadataTableM m -> MetadataTableM m
addStringA str = snd . addMetadata (ValMdString <$> str)

addString :: Applicative m => String -> MetadataTableM m -> MetadataTableM m
addString str = addStringA (pure str)

addStringsA :: Applicative m
           => [m String]
           -> MetadataTableM m
           -> MetadataTableM m
addStringsA strs mt = foldl (flip addStringA) mt strs

addLoc :: Applicative m
       => Bool
       -> PDebugLoc
       -> MetadataTableM m
       -> MetadataTableM m
addLoc isDistinct loc mt = nameNode False isDistinct ix mt'
  where (ix, mt') = addMetadata (ValMdLoc loc) mt

-- addLoc :: Applicative f
--        => Bool -> f PDebugLoc -> f MetadataTableM m -> f MetadataTable
-- addLoc isDistinct loc mt = nameNode False isDistinct <$> ix <*> mt'
--   where (ix, mt') = addMetadata (ValMdLoc loc) mt

-- addLoc :: Bool -> PDebugLoc -> MetadataTableM m -> MetadataTable
-- addLoc isDistinct loc mt = nameNode False isDistinct ix mt'
--   where (ix, mt') = addMetadata (ValMdLoc loc) mt

addDebugInfo :: Applicative m
             => Bool
             -> DebugInfo' Int
             -> MetadataTableM m
             -> MetadataTableM m
addDebugInfo isDistinct di mt = nameNode False isDistinct ix mt'
  where
  (ix,mt') = addMetadata (ValMdDebugInfo di) mt

-- | Add a new node, that might be distinct.
addNode :: Applicative m
        => Bool
        -> [Maybe PValMd]
        -> MetadataTableM m -> MetadataTableM m
addNode isDistinct vals mt = nameNode False isDistinct ix mt'
  where (ix, mt') = addMetadata (ValMdNode vals) mt

addOldNode :: Applicative m
           => Bool
           -> [Typed PValue]
           -> MetadataTableM m
           -> MetadataTableM m
addOldNode fnLocal vals mt = nameNode fnLocal False ix mt'
  where (ix, mt') = addMetadata (ValMdNode [ Just (ValMdValue tv) | tv <- vals ]) mt

addOldNodeA :: Applicative f
            => Bool
            -> f [Typed PValue]
            -> MetadataTableM f
            -> MetadataTableM f
addOldNodeA fnLocal vals mt = nameNode fnLocal False ix mt'
  where (ix, mt') = addMetadata (ValMdNode [ Just (ValMdValue tv) | tv <- vals ]) mt

-- | Either (1) find a value in the 'mtNodes' and return its TODO,
--   or use a forward reference to the value.
mdForwardRef :: LookupMd m => MetadataTableM m -> Int -> m PValMd
mdForwardRef mt ix =
  case Map.lookup ix (mtNodes mt) of
    Just x  -> fmap thd x
    Nothing ->
      withLookup ix $
        \case
          Typed { typedValue = ValMd md } -> md
          tv                              -> ValMdValue tv
  where thd (_, _, r) = ValMdRef r -- "third"

mdForwardRefOrNull :: LookupMd m
                   => MetadataTableM m
                   -> Int
                   -> Maybe (m PValMd)
mdForwardRefOrNull mt ix | ix > 0 = Just (mdForwardRef mt (ix - 1))
                         | otherwise = Nothing

-- | This version is useful in 'Compose'd blocks
mdForwardRefOrNull' :: LookupMd m
                    => MetadataTableM m -> Int -> m (Maybe PValMd)
mdForwardRefOrNull' x = commuteMaybe . mdForwardRefOrNull x

mdNodeRef :: Functor f => [String] -> MetadataTableM f -> Int -> f Int
mdNodeRef cxt mt ix =
  case Map.lookup ix (mtNodes mt) of
    Just x  -> fmap thd x
    Nothing -> X.throw (BadValueRef cxt ix) -- TODO: better error messages
  where thd (_, _, z) = z

mdString :: LookupMd m => [String] -> MetadataTableM m -> Int -> m String
mdString cxt mt ix =
  case mdStringOrNull cxt mt ix of
    Just str -> str
    Nothing  -> X.throw (BadValueRef cxt ix)

mdStringOrNull :: LookupMd m
               => [String]
               -> MetadataTableM m
               -> Int
               -> Maybe (m String)
mdStringOrNull cxt mt ix =
  case mdForwardRefOrNull mt ix of
      Just y  -> pure $ flip fmap y $
        \case
          (ValMdString str) -> str
          _                 -> X.throw (BadTypeRef cxt ix)
      Nothing -> Nothing

-- | This version is useful in 'Compose'd blocks
mdStringOrNull' :: LookupMd m
                => [String] -> MetadataTableM m -> Int -> m (Maybe String)
mdStringOrNull' cxt mt = commuteMaybe . mdStringOrNull cxt mt

mkMdRefTable :: MetadataTable -> MdRefTable
mkMdRefTable mt = Map.mapMaybe step (mtNodes mt)
  where step (fnLocal, _, ix) = do
          guard (not fnLocal)
          return ix

-- ** LookupMd

-- | @LookupMd m a
--   = Lookup m (Typed PValue) a
--   = ReaderM m (Int -> m (Typed PValue)) a
--   = (Int -> m (Typed PValue)) -> m a@
type LookupMd m = Lookup m Int (Typed PValue)

-- ** PartialMetadata

-- | The fields wrapped in a @m@ are the ones that use forward references while
-- they're being parsed.
data PartialMetadata m = PartialMetadata
  { pmEntries          :: MetadataTableM m
  , pmNamedEntries     :: Map.Map String      (m [Int])
  , pmGlobalAttachments:: PGlobalAttachments' (m (Map.Map KindMd PValMd))
  , pmNextName         :: Maybe String
  , pmInstrAttachments :: InstrMdAttachments
  , pmFnAttachments    :: PFnMdAttachments
  }

emptyPartialMetadata :: Functor m
                     => Int {- ^ globals seen so far -}
                     -> MdTable
                     -> PartialMetadata m
emptyPartialMetadata globals es = PartialMetadata
  { pmEntries           = emptyMetadataTable' globals es
  , pmNamedEntries      = Map.empty
  , pmNextName          = Nothing
  , pmInstrAttachments  = Map.empty
  , pmFnAttachments     = Map.empty
  , pmGlobalAttachments = Map.empty
  }

-- updateMetadataTable :: (MetadataTableM f -> MetadataTableM f)
--                     -> PartialMetadata f
--                     -> PartialMetadata f
-- updateMetadataTable g pm = pm { pmEntries = g $ pmEntries pm }

-- updateMetadataTableA :: f (MetadataTableM f -> MetadataTableM f)
--                      -> PartialMetadata f
--                      -> PartialMetadata f
-- updateMetadataTableA g pm = pm { pmEntries = g <*> pure (pmEntries pm) }


addGlobalAttachmentsA :: Applicative m
                      => Symbol                    -- ^ name of the global to attach to
                      -> m (Map.Map KindMd PValMd) -- ^ metadata references to attach
                      -> PartialMetadata m
                      -> PartialMetadata m
addGlobalAttachmentsA sym mds pm =
  pm { pmGlobalAttachments = Map.insert sym mds (pmGlobalAttachments pm) }

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

nameMetadataA :: Applicative m
              => m [Int] -> PartialMetadata m -> Parse (PartialMetadata m)
nameMetadataA val pm = case pmNextName pm of
  Just name -> return $! pm
    { pmNextName     = Nothing
    , pmNamedEntries = Map.insert name val (pmNamedEntries pm)
    }
  Nothing -> fail "Expected a metadata name"


namedEntries :: (LookupMd m) => PartialMetadata m -> m [NamedMd]
namedEntries  =
  pmNamedEntries                       -- Map String (m [Int])
  >>> Map.toList                       -- [(String, m [Int])]
  >>> map (\(s, i) -> NamedMd s <$> i) -- [m NamedMd]
  >>> sequence                         -- m [NamedMd]

type PKindMd               = Int
type InstrMdAttachments    = Map.Map Int [(KindMd,PValMd)]
type PFnMdAttachments      = Map.Map PKindMd PValMd
type PGlobalAttachments' v = Map.Map Symbol v
type PGlobalAttachments    = Map.Map Symbol (Map.Map KindMd PValMd)
