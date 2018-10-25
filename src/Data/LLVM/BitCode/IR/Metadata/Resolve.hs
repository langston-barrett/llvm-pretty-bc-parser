{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
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

import qualified Data.Text as Text
import           Data.Text (Text)
import           Control.Arrow ((>>>))
import           Lens.Micro hiding (ix)
import           Data.Functor.Compose (getCompose)
import qualified Data.Set as Set
import qualified Data.Map as Map
import           Data.Map (Map)
import           MonadLib
import           MonadLib.Monads

import           Data.LLVM.BitCode.Parse
import           Text.LLVM.AST
import           Text.LLVM.Labels (relabel)

import           Data.LLVM.BitCode.IR.Metadata.Lookup
import           Data.LLVM.BitCode.IR.Metadata.Table

import           Debug.Trace

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

namedEntries :: Applicative m => PartialMetadata m -> m [NamedMd]
namedEntries =
  (^. pmNamedEntries)                       -- Map String (m [Int])
  >>> Map.toList                            -- [(String, m [Int])]
  >>> traverse (\(s, i) -> NamedMd s <$> i) -- m [NamedMd]

-- | Partition unnamed entries into global and function local unnamed entries.
unnamedEntries :: PartialMetadata Id -> ([PartialUnnamedMd],[PartialUnnamedMd])
unnamedEntries pm = foldl resolveNode ([],[]) $ Map.toList (runId <$> mt ^. mtNodes)
  where
  mt = pm ^. pmEntries

  resolveNode (gs,fs) (ref,(fnLocal,d,ix)) = case lookupNode ref d ix of
    Just pum | fnLocal   -> (gs,pum:fs)
             | otherwise -> (pum:gs,fs)

    -- TODO: is this silently eating errors with metadata that's not in the
    -- value table?
    Nothing              -> (gs,fs)

  lookupNode ref d ix = do
    Typed { typedValue = ValMd v } <- lookupValueTableAbs ref (runId <$> mt ^. mtEntries )
    return PartialUnnamedMd
      { pumIndex  = ix
      , pumValues = v
      , pumDistinct = d
      }

-- ** Resolve

-- We pass in a "monadic lookup function" (lookupStateExcept) that simply looks
-- to see if the request is already "cached" in the @Map@ which is the state. If
-- not, it raises an exception, short-circuiting the evaluation of that
-- reference.
--
-- When are things added to the state? If a node that has no forward references
-- is passed the lookup function, it will never call it. We then add that
-- finalized node to the state table (see resolveAll').
--
-- The raised exception is the key of the referenced node.

tell :: forall m. (WriterM m [Text]) => [Text] -> m()
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
           , Text.pack (show $ Map.keysSet st)
           ]
      raise i

-- | Our concrete applicative stack, used to instantiate 'lookupStateExcept'
type SEW k v = ExceptionT k (StateT (Map k v) (Writer [Text]))

runSEW :: SEW k v a -> Map k v -> (Either k a, Map k v, [Text])
runSEW sew m =
  let ((x, y), z) = runWriter $ runStateT m $ runExceptionT sew
  in (x, y, z)


-- type StateExceptT s e m    = StateT s (ExceptionT e m)
-- type StateExcept  s e      = StateExceptT s e Id
-- type StateExceptMapT k v f = StateExceptT (Map k v) k f
-- type StateExceptMap k v    = StateExcept (Map k v) k

-- | Take a 'Traversable' containing values that need an "effectful lookup
-- table". Pass it 'lookupStateExcept' and run it with the current state. If it
-- raises an exception, put that in the value.
resolveSome :: forall m k v f a. ( Show k           -- Logging
                                 , Show v           -- Logging
                                 , Show a           -- Logging
                                 , WriterM m [Text] -- Logging
                                 , Ord k            -- Map
                                 , Traversable f
                                 , StateM m (Map k v)
                                 )
            => f (Lookup (SEW k v) k v a)
            -> m (f (Either k a))
resolveSome fun =
  let -- First, feed lookupStateExcept through all the readers.
      mp' :: f (SEW k v a)
      mp' = fmap (runReader lookupStateExcept . getCompose) fun
  in -- For each monadic value,
     forM mp' $ \sev -> do -- sev: "state-except value"

      st <- get
      -- Run the value with the current state.

      let (result, newState, log_) = runSEW sev st
      sets_ (Map.union newState)

      case result of
        -- If it raised an exception, just feed that on through.
        Left i  -> do
          tell log_
          pure $ Left i
        -- Otherwise, merge any updated state (resolved references),
        Right v -> do
          tell [ "Resolved all references in node: "
               , Text.pack (show v)
               ]
          sets_ (Map.union newState)
          -- And pass the rest on through.
          pure $ Right v

-- | A version of 'resolveAll' that updates the state with intermediate results.
resolveAll' :: forall m k v. ( Show k           -- Logging
                             , Show v           -- Logging
                             , WriterM m [Text] -- Logging
                             , Ord k            -- Map
                             , StateM m (Map k v)
                             )
            => Map k (Lookup (SEW k v) k v v)
            -> m (Either [(k, k)] (Map k v))
resolveAll' mp = do

  (lefts, rights) <- Map.mapEither id <$> resolveSome mp

  -- Take the resolved references and add them to the state.
  sets_ (Map.union rights)

  -- This condition guards against infinite loops: If there's no hope that
  -- updating the state further (with a recursive call) would lead to
  -- resolution, it returns the current 'lefts'.
  if   not $ Set.null $ Set.difference (Set.fromList $ Map.elems lefts) (Map.keysSet mp)
  then do
    tell [ "The state has the following keys:"
         , Text.pack $ show (Set.toList $ Map.keysSet mp)
         , "However, I need the following references:"
         , Text.pack $ show (Map.elems lefts)
         ]
    pure $ Left (Map.toList lefts)
  else
    if   Map.size lefts == 0 -- If everything was resolved,
    then Right <$> get       -- then we're done, and the state holds the results.
    else do
     tell ["resolveAll': recursing"]
     resolveAll' mp      -- Otherwise, repeat with new state

-- | Call 'resolveSome' and hope all the references are in the state.
--
-- If some node @a@ references a node @b@ which doesn't appear in the state (due
-- to an implementation error in the parser or malformed input), then this
-- @Left s@ where @s@ contains @(a, b)@.
resolveAll :: forall m k v k' v'. ( Show k           -- Logging
                                  , Show k'          -- Logging
                                  , Show v           -- Logging
                                  , Show v'          -- Logging
                                  , WriterM m [Text] -- Logging
                                  , Ord k            -- Map
                                  , Ord k'           -- Map
                                  , StateM m (Map k v)
                                  )
           => Map k' (Lookup (SEW k v) k v v')
           -> m (Either [(k', k)] (Map k' v'))
resolveAll mp = do
  put ["resolveAll"]
  (lefts, rights) <- Map.mapEither id <$> resolveSome mp
  pure $ if   not (Map.null lefts)
         then Left (Map.toList lefts)
         else Right rights
