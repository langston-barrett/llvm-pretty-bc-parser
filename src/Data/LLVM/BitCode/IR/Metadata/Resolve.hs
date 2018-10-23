{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      : Data.LLVM.BitCode.IR.Metadata.Resolve
Description : Resolve forward references in metadata blocks
Copyright   : (c) Galois, Inc 2018
License     : BSD-3
Maintainer  : atomb@galois.com
Stability   : experimental
-}

module Data.LLVM.BitCode.IR.Metadata.Resolve where

-- import qualified Data.Text as Text
-- import           Data.Text (Text)
import qualified Data.Map as Map
import           Data.Map (Map)
import           MonadLib
import           MonadLib.Monads
import           Data.Either (partitionEithers)
import           Data.Maybe (catMaybes)

import           Data.LLVM.BitCode.Parse
import           Text.LLVM.AST
import           Text.LLVM.Labels (relabel)

import           Data.LLVM.BitCode.IR.Metadata.Table
import           Data.LLVM.BitCode.IR.Metadata.Lookup

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
    { umIndex  = pumIndex pum
    , umValues = v
    , umDistinct = pumDistinct pum
    }

finalizePValMd :: PValMd -> Parse ValMd
finalizePValMd = relabel (const requireBbEntryName)

-- | Partition unnamed entries into global and function local unnamed entries.
unnamedEntries :: forall m. LookupMd m
               => PartialMetadata m -> m ([PartialUnnamedMd], [PartialUnnamedMd])
unnamedEntries pm =
  partitionEithers . catMaybes <$>
    (traverse resolveNode =<< (Map.toList . mtNodes <$> mt))
  where
    mt = pmEntries pm

    resolveNode :: (Int, (Bool, Bool, Int)) -> m (Maybe (Either PartialUnnamedMd PartialUnnamedMd))
    resolveNode (ref, (fnLocal, d, ix)) =
      flip fmap (lookupNode ref d ix) $
        \case
          Just pum | fnLocal   -> Just $ Left  pum
                   | otherwise -> Just $ Right pum

          -- TODO: is this silently eating errors with metadata that's not in the
          -- value table?
          Nothing              -> Nothing

    lookupNode :: Int -> Bool -> Int -> m (Maybe PartialUnnamedMd)
    lookupNode ref d ix =
      let looked :: m (Maybe (Typed PValue))
          looked = lookupValueTableAbs ref . mtEntries <$> mt
      in flip fmap looked $
          \case
            Just Typed{ typedValue = ValMd v } ->
              return PartialUnnamedMd
                { pumIndex  = ix
                , pumValues = v
                , pumDistinct = d
                }
            _ -> Nothing

type ParsedMetadata =
  ( [NamedMd]
  , ([PartialUnnamedMd], [PartialUnnamedMd])
  , InstrMdAttachments
  , PFnMdAttachments
  , PGlobalAttachments
  )

parsedMetadata :: LookupMd m => PartialMetadata m -> m ParsedMetadata
parsedMetadata pm =
  (,,,,)
  <$> namedEntries pm
  <*> unnamedEntries pm
  <*> pure (pmInstrAttachments pm)
  <*> pure (pmFnAttachments pm)
  <*> pmGlobalAttachments pm

-- ** Resolve monad stack

-- | @RWST = 'ReaderT' + 'WriterT' + 'StateT'@
type RWST r w s m a = (ReaderT r (WriterT  w (StateT s m))) a

type ResolveT m a =
  RWST (Int -> m (Typed PValue)) [String] (Map Int (Typed PValue)) m a

-- | Throws away the final state
runResolveT :: Monad m
            => Map Int (Typed PValue)
            -> (Int -> m (Typed PValue))
            -> ResolveT m a
            -> m (a, [String])
runResolveT m i rt = fst <$> runStateT m (runWriterT (runReaderT i rt))

-- ** Resolve

-- The algorithm is deceptively simple:
-- We pass in a "monadic lookup function" that simply looks to see if the
-- request is already "cached" in the @Map@ which is the state. If not,
-- it raises an exception, short-circuiting the evaluation of that reference.
--
-- When are things added to the state? If a node that has no forward references
-- is passed the lookup function, it will never call it. We then add that
-- finalized node to the state table.
--
-- The raised exception is the key of the referenced node

-- | Lookup a key from the state, raising an exception if it's not found
lookupStateExcept :: (Ord k, StateM m (Map k v), ExceptionM m k)
                  => k -> m v
lookupStateExcept i = do
  st <- get
  case Map.lookup i st of
    Just v  -> pure v
    Nothing -> raise i

-- | Abstract monad stack
runLookup :: forall m i v a. (Ord i, StateM m (Map i v), ExceptionM m i)
          => ReaderT (i -> m v) m a
          -> m a
runLookup = runReaderT lookupStateExcept

-- | Concrete monad stack
runLookup' :: forall k v a. (Ord k)
          => (forall m. ReaderT (k -> m v) m a)
          -> (ExceptionT k (State (Map k v))) a
          -- -> (StateT (Map k v) (Exception k)) a
runLookup' = runLookup

loop :: forall k v a. (Ord k)
     => (forall m. ReaderT (k -> m v) m (Map k v))
     -> k
     -> State (Map k v) (Either Int v)
loop c k = do
  foo <- run c
  case foo of
    Left  i ->
      -- It couldn't be looked up in the state, so recurse
      -- on the exception value
      loop c i
    Right j -> do
      sets_ (Map.insert k j)
      _
      -- pure (Right j)
  where run :: (forall m. ReaderT (k -> m v) m (Map k v))
            -> State (Map k v) (Either k (Map k v))
        run ll = runExceptionT $ runLookup' ll

-- alg :: forall i v a. (Ord i)
--     => (forall m. ReaderT (i -> m v) m (Map i v))
--     -> State (Map i v) a
-- alg l = do
--   r <- run l
--   case r of
--     Left i  -> _
--       -- x <- run i
--     Right j -> _
--   where run :: (forall m. ReaderT (i -> m v) m (Map i v))
--             -> State (Map i v) (Either i (Map i v))
--         run ll = runExceptionT $ runLookup' ll

specialize :: Monad n
           => (forall m. ReaderM m i => m a)
           -> ReaderT i n a
specialize r = r

