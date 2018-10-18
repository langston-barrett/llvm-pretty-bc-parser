{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-|
Module      : Data.LLVM.BitCode.IR.Metadata.MetadataTable
Description : The parsing state for metadata blocks
Copyright   : (c) Galois, Inc 2018
License     : BSD-3
Maintainer  : atomb@galois.com
Stability   : experimental

It defines 'PartialMetadataTable', which is used internally while processing a
metadata block, and then resolved into a 'MetadataTable'.
-}
module Data.LLVM.BitCode.IR.Metadata.MetadataTable where

import Data.LLVM.BitCode.Parse
import Text.LLVM.AST
import Text.LLVM.Labels

import           MonadLib (ReaderM, ask, runId)
import           Control.Monad (guard)
import qualified Data.Map as Map
import           Data.Map (Map)

-- Parsing State ---------------------------------------------------------------

data MetadataTable' a = MetadataTable
  { mtEntries   :: MdTable' a
  , mtNextNode  :: !Int
  , mtNodes     :: Map Int (Bool,Bool,Int)
                   -- ^ The entries in the map are: is the entry function local,
                   -- is the entry distinct, and the implicit id for the node.
                   -- "distinct" is a keyword in LLVM IR, see the language spec.
  } deriving (Eq, Functor, Show)

type MetadataTable = MetadataTable' (Typed PValue)

emptyMetadataTable :: Int         -- ^ Globals seen so far
                   -> MdTable' a  -- ^ Table so far
                   -> MetadataTable' a
emptyMetadataTable globals es = MetadataTable
  { mtEntries   = es
  , mtNextNode  = globals
  , mtNodes     = Map.empty
  }

metadata :: PValMd -> Typed PValue
metadata  = Typed (PrimType Metadata) . ValMd

-- | Add a value to the metadata table, returning its ID and the new table
addMetadata' :: a -> MetadataTable' a -> (Int, MetadataTable' a)
addMetadata' val mt = (ix, mt { mtEntries = es' })
  where (ix,es') = addValue' val (mtEntries mt)

addMetadata :: PValMd -> MetadataTable -> (Int, MetadataTable)
addMetadata val mt = (ix, mt { mtEntries = es' })
  where (ix,es') = addValue' (metadata val) (mtEntries mt)

addMdValue' :: (Typed PValue -> a) -> Typed PValue -> MetadataTable' a -> MetadataTable' a
addMdValue' f tv mt = mt { mtEntries = addValue (f tv') (mtEntries mt) }
  where
  -- explicitly make a metadata value out of a normal value
  tv' = Typed { typedType  = PrimType Metadata
              , typedValue = ValMd (ValMdValue tv)
              }

addMdValue_ :: Typed PValue -> MetadataTable -> MetadataTable
addMdValue_ = addMdValue' id

addMdValue :: Applicative m
           => Typed PValue
           -> MetadataTableUnresolved m
           -> MetadataTableUnresolved m
addMdValue = addMdValue' pure

nameNode :: Bool
         -> Bool -- ^ Whether or not this node is distinct (see @MetadataTable@)
         -> Int  -- ^ Index to insert at
         -> MetadataTable' a
         -> MetadataTable' a
nameNode fnLocal isDistinct ix mt = mt
  { mtNodes    = Map.insert ix (fnLocal,isDistinct,mtNextNode mt) (mtNodes mt)
  , mtNextNode = mtNextNode mt + 1
  }

-- addString :: String -> MetadataTable -> MetadataTable
-- addString str = snd . addMetadata (ValMdString str)

addString :: Applicative m
          => String
          -> MetadataTableUnresolved m
          -> MetadataTableUnresolved m
addString str untab =
  snd $ addMetadata' (pure $ metadata $ ValMdString str) untab

-- addStrings :: [String] -> MetadataTable -> MetadataTable
-- addStrings strs mt = foldl (flip addString) mt strs

addLoc :: Bool -> PDebugLoc -> MetadataTable -> MetadataTable
addLoc isDistinct loc mt = nameNode False isDistinct ix mt'
  where (ix,mt') = addMetadata (ValMdLoc loc) mt

addLoc' :: WithForwardMdRef m
        => Bool                      -- ^ Is this metadata "distinct"?
        -> m PDebugLoc               -- ^ Debug location (with forward refs)
        -> MetadataTableUnresolved m -- ^ Current table
        -> MetadataTableUnresolved m
addLoc' isDistinct loc mt = nameNode False isDistinct ix mt'
  where (ix, mt') = addMetadata' (metadata . ValMdLoc <$> loc) mt

addDebugInfo' :: Applicative m
              => Bool           -- ^ Is this debug info "distinct"?
              -> m (DebugInfo' Int)
              -> MetadataTable' (m (Typed PValue))
              -> MetadataTable' (m (Typed PValue))
addDebugInfo' isDistinct di mt = nameNode False isDistinct ix mt'
  where (ix,mt') = addMetadata' (metadata . ValMdDebugInfo <$> di) mt

addDebugInfo :: Bool           -- ^ Is this debug info "distinct"?
             -> DebugInfo' Int
             -> MetadataTable
             -> MetadataTable
addDebugInfo isDistinct di mt =
  runId <$> addDebugInfo' isDistinct (pure di) (pure <$> mt)

-- | Add a new node, that might be distinct.
addNode :: Bool -> [Maybe PValMd] -> MetadataTable -> MetadataTable
addNode isDistinct vals mt = nameNode False isDistinct ix mt'
  where
  (ix,mt') = addMetadata (ValMdNode vals) mt

addNodeF :: Functor m
         => Bool
         -> m [Maybe PValMd]
         -> MetadataTable' (m (Typed PValue)) -> MetadataTable' (m (Typed PValue))
addNodeF isDistinct vals mt = nameNode False isDistinct ix mt'
  where (ix, mt') = addMetadata' (metadata . ValMdNode <$> vals) mt

addOldNode :: Bool -> [Typed PValue] -> MetadataTable -> MetadataTable
addOldNode fnLocal vals mt = nameNode fnLocal False ix mt'
  where
  (ix,mt') = addMetadata (ValMdNode [ Just (ValMdValue tv) | tv <- vals ]) mt

mkMdRefTable :: MetadataTable -> MdRefTable
mkMdRefTable mt = Map.mapMaybe step (mtNodes mt)
  where
  step (fnLocal,_,ix) = do
    guard (not fnLocal)
    return ix

-- Forward references ---------------------------------------------------------

-- -- | Jump forward to parse a metadata node
-- mdForwardRef :: Monad m
--              => Int            -- ^ Index of the node to parse
--              -> UnresolvedMetadata m
-- mdForwardRef i lookup =
--   lookup i >>=
--     \case v
--       Typed { typedValue = ValMd md } -> pure md
--       tv                              -> pure $ ValMdValue tv

  -- fromMaybe <$> fallback <*> pure nodeRef
  -- where
  -- fallback          = forwardRef cxt ix (mtEntries mt) >>= \case
  --                       Typed { typedValue = ValMd md } -> pure md
  --                       tv                              -> pure $ ValMdValue tv
  -- reference (_,_,r) = ValMdRef r
  -- nodeRef           = reference `fmap` Map.lookup ix (mtNodes mt)

-- | Either (1) find a value in the 'mtNodes' and return its TODO,
--   or use a forward reference to the value.
mdForwardRef :: WithForwardMdRef m => MetadataTable' v -> Int -> m PValMd
mdForwardRef mt ix =
  case nodeRef of
    Just x  -> pure x
    Nothing ->
      withResolveRef ix $
        \case
          Typed { typedValue = ValMd md } -> md
          tv                              -> ValMdValue tv
  where
    thd (_, _, r) = ValMdRef r -- "third"
    nodeRef       = thd `fmap` Map.lookup ix (mtNodes mt)


mdForwardRefOrNull :: WithForwardMdRef m
                   => MetadataTable' a
                   -> Int
                   -> Maybe (m PValMd)
mdForwardRefOrNull mt ix | ix > 0 = Just (mdForwardRef mt (ix - 1))
                         | otherwise = Nothing

mdNodeRef :: MetadataTable -> Int -> Maybe Int
mdNodeRef mt ix = thd <$> Map.lookup ix (mtNodes mt)
  where thd (_, _, x) = x

mdString :: WithForwardMdRef m => MetadataTable -> Int -> m String
mdString mt ix =
  case mdStringOrNull mt ix of
    Just str -> str
    Nothing  -> error "TODO"

mdStringOrNull :: forall m. WithForwardMdRef m
               => MetadataTable
               -> Int
               -> Maybe (m String)
mdStringOrNull mt ix =
  case mdForwardRefOrNull mt ix of
      Just y  -> pure $ flip fmap y $
        \case
          (ValMdString str) -> str
          _                 -> error "TODO"
      Nothing -> Nothing

-- Partial metadata ------------------------------------------------------------

-- | A computation that depends on having access to a "monadic lookup table"
type LookupTable m n i v = ReaderM m (i -> n v)

-- | A computation that depends on forward references to be resolved
-- (monadically) later.
--
-- References are resolved in "Data.LLVM.BitCode.IR.Metadata.Resolve".
--
-- We could replace @LookupTable m m@ by @BaseM n m => LookupTable m n@.
--
-- WithForwardRef m v a
-- = ReadMFun m m Int v a
-- = (Int -> m v) -> m a
--
type WithForwardRef m v = LookupTable m m Int v

-- | WithForwardMdRef m a
--   = WithForwardRef m (Typed PValue) a
--   = LookupTable m m Int (Typed PValue) a
--   = ReaderM m (Int -> m (Typed PValue)) a
--   = (Int -> m (Typed PValue)) -> m a
type WithForwardMdRef m = WithForwardRef m (Typed PValue)

type MetadataTableUnresolved m = WithForwardMdRef m => MetadataTable' (m (Typed PValue))

-- | In case we ever need to print an incomplete table (e.g. while debugging)
-- instance Show (UnresolvedMetadata m) where
--   show _ = "[Metadata with unresolved references]"

-- | Resolve a single forward reference.
--
-- (If ReaderT were an "applicative transformer", f would only need to be a
-- 'Functor'.)
withResolveRef :: forall m a b. WithForwardRef m b
               => Int      -- ^ Index to resolve
               -> (b -> a) -- ^ Function of the result
               -> m a      -- ~=~ ReaderT (Int -> f b) f a
withResolveRef i cont = do
  look <- ask
  cont <$> look i

-- | The partial metadata table contains, instead of @Typed PValue@s,
--   metadata nodes with unresolved references.
--
--   The references will be resolved in the monad m.
data PartialMetadata m = PartialMetadata
  { pmEntries          :: MetadataTableUnresolved m
    -- ^ A metadata table with unresolved references
  , pmNamedEntries     :: Map.Map String [Int]
  , pmNextName         :: Maybe String
  , pmInstrAttachments :: InstrMdAttachments
  , pmFnAttachments    :: PFnMdAttachments
  , pmGlobalAttachments:: PGlobalAttachments
  }

emptyPartialMetadata :: forall m. Monad m
                     => Int -- ^ globals seen so far
                     -> MdTable
                     -> PartialMetadata m
emptyPartialMetadata globals es = PartialMetadata
  { pmEntries          = emptyMetadataTable globals es'
  , pmNamedEntries     = Map.empty
  , pmNextName         = Nothing
  , pmInstrAttachments = Map.empty
  , pmFnAttachments    = Map.empty
  , pmGlobalAttachments= Map.empty
  }
  where es' = fmap pure es

updateMetadataTable :: WithForwardMdRef m
                    => (MetadataTable' (m (Typed PValue)) -> MetadataTable' (m (Typed PValue)))
                    -> (PartialMetadata m -> PartialMetadata m)
updateMetadataTable f pm = pm { pmEntries = f (pmEntries pm) }

addGlobalAttachments ::
  Symbol {- ^ name of the global to attach to ^ -} ->
  Map KindMd PValMd {- ^ metadata references to attach ^ -} ->
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
unnamedEntries :: PartialMetadata -> ([PartialUnnamedMd],[PartialUnnamedMd])
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

-- parsedMetadata :: PartialMetadata -> ParsedMetadata
-- parsedMetadata pm =
--   ( namedEntries pm
--   , unnamedEntries pm
--   , pmInstrAttachments pm
--   , pmFnAttachments pm
--   , pmGlobalAttachments pm
--   )
