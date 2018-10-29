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

import           Data.Functor.Compose (Compose(..))
import           MonadLib
import           MonadLib.Monads

-- ** Lookup

-- | A computation that depends on having access to a "effectful lookup table"
--
-- We are most often interested in when @f@ is an 'Applicative', so that
-- 'Lookup' is as well.
type Lookup f i v = (Compose (Reader (i -> f v)) f)

-- | In case we ever need to print an incomplete table (e.g. while debugging)
-- instance Show (UnresolvedMetadata m) where
--   show _ = "[Metadata with unresolved references]"

withLookup :: (Functor f)
           => i        -- ^ Index to resolve
           -> (v -> a) -- ^ Function of the result
           -> Lookup f i v a
withLookup i cont = Compose $ fmap cont . ($i) <$> ask


lookup :: (Functor f)
       => i        -- ^ Index to resolve
       -> Lookup f i v v
lookup = flip withLookup id
