{-# LANGUAGE LambdaCase #-}
{-|
Module      : Data.LLVM.BitCode.IR.Metadata.Applicative
Description : Utilities for working with composed applicative functions
Copyright   : (c) Galois, Inc 2018
License     : BSD-3
Maintainer  : atomb@galois.com
Stability   : experimental
-}

module Data.LLVM.BitCode.IR.Metadata.Applicative
  ( (<$$>)
  , (<**>)
  , (<$>>)
  , (<<$>)
  , (<<*>)
  , (<*>>)
  , tupleA
  , commuteMaybe
  ) where

import Data.Functor.Compose (Compose(..))

-- | Useful for avoiding writing 'Compose'.
(<$$>) :: (Functor f, Functor g)
       => (a -> b) -> f (g a) -> Compose f g b
h <$$> x = h <$> Compose x

-- | Useful for avoiding writing 'Compose'.
(<**>) :: (Applicative f, Applicative g)
       => Compose f g (a -> b) -> f (g a) -> Compose f g b
h <**> x = h <*> Compose x

(<$>>) :: (Applicative f, Functor g)
       => (a -> b) -> g a -> Compose f g b
h <$>> x = h <$> Compose (pure x)

(<<$>) :: (Functor f, Applicative g)
       => (a -> b) -> f a -> Compose f g b
h <<$> x = h <$> Compose (pure <$> x)

-- | Useful for avoiding writing 'pure'.
-- (i.e. only some parts of your long applicative chain use both effects)
(<<*>) :: (Applicative f, Applicative g)
       => Compose f g (a -> b) -> f a -> Compose f g b
h <<*> x = h <*> Compose (pure <$> x)

-- | Useful for avoiding writing 'pure'.
-- (i.e. only some parts of your long applicative chain use both effects)
(<*>>) :: (Applicative f, Applicative g)
       => Compose f g (a -> b) -> g a -> Compose f g b
h <*>> x = h <*> Compose (pure x)

-- | You can pull a functor out of a tuple if its an applicative
tupleA :: Applicative f => (f a, f b) -> f (a, b)
tupleA (f, s) = (,) <$> f <*> s

-- | Commute an applicative with Maybe
commuteMaybe :: Applicative f => Maybe (f a) -> f (Maybe a)
commuteMaybe (Just val) = Just <$> val
commuteMaybe Nothing    = pure Nothing
