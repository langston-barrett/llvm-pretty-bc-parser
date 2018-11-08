{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Strict #-}

{-|
Module      : Data.LLVM.BitCode.IR.Metadata.Resolve
Description : Resolve forward references in metadata blocks
Copyright   : (c) Galois, Inc 2018
License     : BSD-3
Maintainer  : atomb@galois.com
Stability   : experimental


We pass in an "effectful lookup function" ('lookupStateExcept') that simply looks
to see if the request is already "cached" in the @Map@ which is the state. If
not, it raises an exception, short-circuiting the evaluation of that reference.
(The raised exception is the key of the referenced node.)

When are things added to the state? If a node that has no forward references
is passed the lookup function, it will never call it. We then add that
finalized node to the state table (see 'resolveAll'').

The Counter datatype tracks progress while resolution is happening. It's
useful for debugging or progress reporting.
-}

module Data.LLVM.BitCode.IR.Metadata.Resolve where

import           Control.Arrow ((***), first, second)
import           Control.Exception.Base (assert)
import           Data.Traversable (for)
import qualified Data.Text as Text
import           Data.Text (Text)
import           Data.Functor.Compose (getCompose)
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import           Data.Map.Strict (Map)
import           MonadLib
import           MonadLib.Monads
import           Data.Validation (Validation(..), fromEither, toEither)
import           Lens.Micro

import           Data.LLVM.BitCode.IR.Metadata.Applicative
import           Data.LLVM.BitCode.IR.Metadata.Counter
import           Data.LLVM.BitCode.IR.Metadata.Lookup

import           Debug.Trace

-- ** Resolve

tell :: forall m. (WriterM m [Text]) => [Text] -> m ()
tell = put . (:[]) . Text.unlines

-- | Lookup a key from the state, raising an exception if it's not found
lookupStateExcept :: ( Show k              -- Logging
                     , Show v              -- Logging
                     , WriterM m [Text]    -- Logging
                     , Ord k               -- Map
                     , StateM m (Map k v)
                     , ExceptionM m k
                     )
                  => k -> m v
lookupStateExcept i = do
  tell [ "Resolving references to key:"
       , Text.pack (show i)
       ]
  st <- get
  case Map.lookup i st of
    Just v  -> do
      tell [ "Resolved reference to key:"
           , Text.pack (show i)
           , "Value was: "
           , Text.pack (show v)
           ]
      pure v
    Nothing -> do
      tell [ "Couldn't resolve reference for key:"
           , Text.pack (show i)
           , "Map contained keys:"
           , Text.pack (show $! Map.keysSet st)
           ]
      raise i

-- | Our concrete applicative stack, used to instantiate 'lookupStateExcept'
type SEW k v = ExceptionT k (StateT (Map k v) (Writer [Text]))

runSEW :: SEW k v a -> Map k v -> (Validation k a, Map k v, [Text])
runSEW sew m =
  let !((x, y), z) = runWriter $! runStateT m $! runExceptionT sew
  in (fromEither x, y, z)

-- type StateExceptT s e m    = StateT s (ExceptionT e m)
-- type StateExcept  s e      = StateExceptT s e Id
-- type StateExceptMapT k v f = StateExceptT (Map k v) k f
-- type StateExceptMap k v    = StateExcept (Map k v) k

resolveOne' :: forall m k v a. ( Show k           -- Logging
                              , Show v           -- Logging
                              , Show a           -- Logging
                              , WriterM m [Text] -- Logging
                              , Ord k            -- Map
                              , StateM m (Counter, Map k v)
                              )
            => Lookup (SEW k v) k v a
            -> m (Validation k a)
resolveOne' sev =
  let -- First, feed lookupStateExcept through the reader.
      sev' :: SEW k v a
      sev' = runReader lookupStateExcept . getCompose $! sev
  in do
    st <- snd <$!> get
    -- Run the value with the current state.

    let (result, newState, log_) = runSEW sev' st
    sets_ (incCtr *** Map.union newState)

    case result of
      -- If it raised an exception, just feed that on through.
      Failure i  -> do
        tell log_
        pure $! Failure i
      -- Otherwise, merge any updated state (resolved references),
      Success v -> do
        tell [ "Resolved all references in node: "
             -- , Text.pack (show v)
             ]
        -- sets_ (Map.union newState)
        -- And pass the rest on through.
        pure $! Success v

resolveOne :: forall m k v a. ( Show k           -- Logging
                              , Show v           -- Logging
                              , Show a           -- Logging
                              , WriterM m [Text] -- Logging
                              , Ord k            -- Map
                              , StateM m (Counter, Map k v)
                              )
           => Lookup (SEW k v) k v a
           -> m (Validation k a)
resolveOne sev = sets_ (first $! const (initCtr 1)) >> resolveOne' sev

-- | Take a 'Traversable' containing values that need an "effectful lookup
-- table". Pass it 'lookupStateExcept' and run it with the current state. If it
-- raises an exception, put that in the value.
resolveSome :: forall m k v f a. ( Show k           -- Logging
                                 , Show v           -- Logging
                                 , Show a           -- Logging
                                 , WriterM m [Text] -- Logging
                                 , Ord k            -- Map
                                 , Traversable f
                                 , Foldable f
                                 , StateM m (Counter, Map k v)
                                 )
            => f (Lookup (SEW k v) k v a)
            -> m (f (Validation k a))
resolveSome f = trace "resolveSome" $! do
  sets_ $! first (const $! initCtr (length f))
  for f $ \sev -> do
    ctr <- fst <$!> get
    tell [ Text.append "Current ctr:" (ppCtr ctr) ]
    resolveOne' $! sev

-- | An analogue of Map.mapEither
mapValidation :: Map a (Validation b c) -> (Map a b, Map a c)
mapValidation = Map.mapEither id . fmap toEither

-- | Run 'resolveSome' and update the state with intermediate results.
--
-- This is the only place where the state can be added to.
-- TODO: This should guarantee that, if successful, the resulting state
-- contains each key in the input map.
--
-- TODO: This should guarantee that, if successful, the resulting map
-- contains identical keys to the input.
resolveAll :: forall m k v. ( Show k           -- Logging
                            , Show v           -- Logging
                            , WriterM m [Text] -- Logging
                            , Ord k            -- Map
                            , StateM m (Counter, Map k v)
                            )
           => Map k (Lookup (SEW k v) k v v)
           -> m (Validation [(k, k)] (Map k v))
resolveAll mp = do
  (lefts, rights) <- mapValidation <$> resolveSome mp

  let assert1 =
        assert (Map.keysSet mp == Set.union (Map.keysSet lefts) (Map.keysSet rights))
  -- Take the resolved references and add them to the state.
  sets_ $! assert1 $! (second $! Map.union rights)

  st <- snd <$> get

  -- If everything was resolved, then the state should contain all the keys of
  -- the original map. Otherwise, it should contain just the ones that were resolved.
  let asserteq stt  = assert $ Map.keysSet mp == Map.keysSet stt
  -- let assertsub stt = assert $ Map.keysSet stt `Set.isSubsetOf` Map.keysSet mp

  -- mp' is mp, but after removing keys that have already been resolved.
  let mp' = Map.withoutKeys mp (Map.keysSet st)

  let needResolved = Set.fromList $ Map.elems lefts
  let haveResolved = Map.keysSet st
  let mightResolve = Map.keysSet mp'
  let diff = Set.difference needResolved (Set.union haveResolved mightResolve)

  if | Map.null lefts ->                     -- If everything was resolved,
         pure $! (Success $! st) -- then we're done; the state holds the results.
     | Map.size lefts == Map.size mp ->
         fail $ unlines [ "Exception: Couldn't resolve anything!"
                        , show lefts
                        ]
     -- This condition guards against infinite loops: If there's no hope that
     -- updating the state further (with a recursive call) would lead to
     -- completion, it returns the current 'lefts'.
     | not $! Set.null $! diff -> do
         tell [ "Metadata contain some references not found in the AST:"
              , Text.pack $! show diff
              ]
         pure $! assert (Set.union haveResolved mightResolve == Map.keysSet mp)
              $! Failure (Map.toList lefts)
     | otherwise -> -- O/w, recurse on only the as-yet unresolved values.
         trace "recursing" $! trace (show $ Map.size lefts)
                           $! resolveAll mp'

-- | Call 'resolveSome' and hope all the references are in the state.
--
-- If some node @a@ references a node @b@ which doesn't appear in the state (due
-- to an implementation error in the parser or malformed input), then this
-- @Left s@ where @s@ contains @(a, b)@.
resolveAllMap :: forall m k v k' v'. ( Show k           -- Logging
                                     , Show k'          -- Logging
                                     , Show v           -- Logging
                                     , Show v'          -- Logging
                                     , WriterM m [Text] -- Logging
                                     , Ord k            -- Map
                                     , Ord k'           -- Map
                                     , StateM m (Counter, Map k v)
                                     )
           => Map k' (Lookup (SEW k v) k v v')
           -> m (Validation [(k', k)] (Map k' v'))
resolveAllMap mp = do
  -- fmap Map.fromList <$>
  --   (resolveAllList . map (\(a, b) -> tupleA2 (pure a, b)) . Map.toList $ mp)
  (lefts, rights) <- trace "mapValidation" $! mapValidation <$!> resolveSome mp
  pure $! if   not     (Map.null lefts)
          then Failure (Map.toList lefts)
          else Success rights

resolveAllList :: forall m k v a. ( Show k           -- Logging
                                  , Show v           -- Logging
                                  , Show a           -- Logging
                                  , WriterM m [Text] -- Logging
                                  , Ord k            -- Map
                                  , StateM m (Counter, Map k v)
                                  )
               => [Lookup (SEW k v) k v a]
               -> m (Validation [k] [a])
resolveAllList l =
  -- We can use 'sequenceA' because of the behavior of 'Validation'
  traverse singletonLeft <$!> resolveSome l
  where singletonLeft (Failure  left) = Failure  [left]
        singletonLeft (Success right) = Success right
