{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      : Data.LLVM.BitCode.IR.Metadata.Resolve
Description : Resolve forward references in metadata blocks
Copyright   : (c) Galois, Inc 2018
License     : BSD-3
Maintainer  : atomb@galois.com
Stability   : experimental

TODO: This module could have better debugging support.
'resolveSome' and 'resolveAll' could be in 'Writer' monads which record progress
in the resolution process.
-}

module Data.LLVM.BitCode.IR.Metadata.Resolve where

-- import qualified Data.Text as Text
-- import           Data.Text (Text)
import           Control.Arrow (first)
import qualified Data.Set as Set
import           Data.Set (Set)
import qualified Data.Map as Map
import           Data.Map (Map)
import           MonadLib
import           MonadLib.Monads
import           Data.Either (partitionEithers)
import           Data.Maybe (catMaybes)

import           Data.LLVM.BitCode.Parse
import           Text.LLVM.AST
import           Text.LLVM.Labels (relabel)

import           Data.LLVM.BitCode.IR.Metadata.Applicative
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
  partitionEithers . catMaybes <$> traverse resolveNode (Map.toList $ mtNodes mt)
  where
    mt = pmEntries pm

    resolveNode :: (Int, m (Bool, Bool, Int)) -> m (Maybe (Either PartialUnnamedMd PartialUnnamedMd))
    resolveNode (ref, s) = do
      (fnLocal, d, ix) <- s
      case lookupNode ref d ix of
        Just pum | fnLocal   -> pure $ Just $ Left pum
                 | otherwise -> pure $ Just $ Right pum

        -- TODO: is this silently eating errors with metadata that's not in the
        -- value table?
        Nothing              -> pure Nothing

    lookupNode :: Int -> Bool -> Int -> Maybe PartialUnnamedMd
    lookupNode ref d ix =
      let looked :: Maybe (Typed PValue)
          looked = lookupValueTableAbs ref (mtEntries mt)
      in case looked of
        Just Typed{ typedValue = ValMd v } ->
          Just PartialUnnamedMd
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
  <*> seqMap (pmGlobalAttachments pm)
  where -- Sequence applicative actions in the keys of a map
        seqMap :: (Ord a, Applicative n) => Map a (n b) -> n (Map a b)
        seqMap m = fmap Map.fromList $ traverse (tupleA . first pure) $ Map.toList m

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

type StateExceptT s e m a = StateT s (ExceptionT e m) a
type StateExcept  s e a   = StateExceptT s e Id a

-- | Take a map with keys that need a lookup table. Pass it 'lookupStateExcept'
-- and run it with the current state. If it raises an exception, put that in the
-- value. If it doesn't, cache the result in the state for the subsequent
-- computations.
resolveSome :: forall k v. (Ord k)
            => (forall m. Map k (ReaderT (k -> m v) m v))
            -> State (Map k v) (Map k (Either k v))
resolveSome mp =
  let -- First, feed lookupStateExcept through all the readers.
      mp' :: Map k (StateExcept (Map k v) k v)
      mp' = fmap (runReaderT lookupStateExcept) mp
  in -- For each key/monadic value pair,
     forM mp' $ \sev -> do -- sev: "state-except value"
      st <- get
      -- Run the value with the current state.
      case runId $ runExceptionT (runStateT st sev) of
        Left i              ->
          -- If it raised an exception, just feed that on through.
          pure $ Left i
        Right (v, newState) -> do
          -- Otherwise, merge any updated state (resolved references),
          sets_ (Map.union newState)
          -- And pass the rest on through.
          pure $ Right v

-- | Repeatedly call 'resolveSome' until every reference has been resolved.
--
-- If some node @a@ references a node @b@ which doesn't appear in the AST (due
-- to an implementation error in the parser or malformed input), then this
-- @Left s@ where @s@ contains @(a, b)@.
resolveAll :: forall k v. (Ord k)
           => (forall m. Map k (ReaderT (k -> m v) m v))
           -> Either (Set (k, k)) (Map k v)
resolveAll mp = fst <$> runState Map.empty $ do
  mp' <- resolveSome mp

  -- Unresolvable references are those that don't appear in the parse tree.
  -- First element is the referencer, second is the referencee.
  let lefts :: Set (k, k)
      lefts = Set.fromList $
        Map.foldrWithKey
          (\k v acc -> either (\ref -> (k, ref):acc) (const acc) v) [] mp'

  if not $ Set.null $ Set.difference (Set.map snd lefts) (Map.keysSet mp')
  then pure $ Left lefts
  else
    if   Set.size lefts == 0    -- If everything was resolved,
    then Right <$> get          -- then we're done, and the state holds the results.
    else pure $ resolveAll mp   -- Otherwise, repeat with new state
