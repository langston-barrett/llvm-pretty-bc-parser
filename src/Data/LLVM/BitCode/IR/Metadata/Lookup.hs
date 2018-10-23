{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-|
Module      : Data.LLVM.BitCode.IR.Metadata.Lookup
Description : A monad for looking up (monadic) values
Copyright   : (c) Galois, Inc 2018
License     : BSD-3
Maintainer  : atomb@galois.com
Stability   : experimental
-}

module Data.LLVM.BitCode.IR.Metadata.Lookup where

import MonadLib (ReaderM, ask)

-- ** Lookup

-- | A computation that depends on having access to a "monadic lookup table"
--
-- We could replace the second @m@ by @n@ and the constraint @BaseM n m@.
--
-- Note that @Lookup m i v :: Constraint@.
type Lookup m i v = ReaderM m (i -> m v)

-- | In case we ever need to print an incomplete table (e.g. while debugging)
-- instance Show (UnresolvedMetadata m) where
--   show _ = "[Metadata with unresolved references]"

-- | Resolve a single forward reference.
withLookupM :: Lookup m i v
            => i          -- ^ Index to resolve
            -> (v -> m a) -- ^ Function of the result
            -> m a
withLookupM i cont = cont =<< ($i) =<< ask

-- | Resolve a single forward reference.
withLookup :: Lookup m i v
           => i        -- ^ Index to resolve
           -> (v -> a) -- ^ Function of the result
           -> m a
withLookup i cont = withLookupM i (pure . cont)
