{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-|
Module      : Data.LLVM.BitCode.IR.Metadata.Applicative
Description : Utilities for working with composed applicative functions
Copyright   : (c) Galois, Inc 2018
License     : BSD-3
Maintainer  : atomb@galois.com
Stability   : experimental

Mnemonic: Extra @<@'s and @>@'s stand for invocations of 'pure', and extra @$@'s
and @*@'s stand for nested '<$>' and '<*>', respectively.
-}

module Data.LLVM.BitCode.IR.Metadata.Applicative
  ( -- * 2-fold composition
    (<$$>)
  , (<**>)
  , (<$>>)
  , (<<$>)
  , (<<*>)
  , (<*>>)
    -- * 3-fold composition
  , (<$$$>)
  , (<***>)
  , (<<<*>)
  , (<*<*>)
    -- * Miscellaneous
  , tupleA2
  , tupleA3
  , commuteMaybe
  ) where

import Data.Functor.Compose (Compose(..))

-- ** 2-fold composition

-- | Useful for avoiding writing 'Compose'.
(<$$>) :: (Functor f, Functor g)
       => (a -> b) -> f (g a) -> f (g b)
h <$$> x = getCompose $ h <$> Compose x

-- | Useful for avoiding writing 'Compose'.
(<**>) :: (Applicative f, Applicative g)
       => f (g (a -> b)) -> f (g a) -> f (g b)
h <**> x = getCompose $ Compose h <*> Compose x

(<$>>) :: (Applicative f, Functor g)
       => (a -> b) -> g a -> f (g b)
h <$>> x = getCompose $ h <$> Compose (pure x)

(<<$>) :: (Functor f, Applicative g)
       => (a -> b) -> f a -> f (g b)
h <<$> x = getCompose $ h <$> Compose (pure <$> x)

-- | Useful for avoiding writing 'pure'.
-- (i.e. only some parts of your long applicative chain use both effects)
(<<*>) :: (Applicative f, Applicative g)
       => f (g (a -> b)) -> f a -> f (g b)
h <<*> x = getCompose $ Compose h <*> Compose (pure <$> x)

-- | Useful for avoiding writing 'pure'.
-- (i.e. only some parts of your long applicative chain use both effects)
(<*>>) :: (Applicative f, Applicative g)
       => f (g (a -> b)) -> g a -> f (g b)
h <*>> x = getCompose $ Compose h <*> Compose (pure x)

-- ** 3-fold composition

newtype Compose2 f g h a = Compose2 { getCompose2 :: f (g (h a)) }
  deriving (Functor)

instance (Applicative f, Applicative g, Applicative h) =>
         Applicative (Compose2 f g h) where
  pure = Compose2 . pure . pure . pure
  (getCompose2 -> f) <*> (getCompose2 -> x) =
    let compose2 z   = Compose (Compose <$> z)
        uncompose2 z = getCompose <$> getCompose z
    in Compose2 (uncompose2 (compose2 f <*> compose2 x))

(<$$$>) :: (Functor f, Functor g, Functor h)
        => (a -> b) -> f (g (h a)) -> f (g (h b))
j <$$$> x = getCompose2 (j <$> Compose2 x)

(<***>) :: (Applicative f, Applicative g, Applicative h)
        => f (g (h (a -> b))) -> f (g (h a)) -> f (g (h b))
h <***> x = getCompose2 $ Compose2 h <*> Compose2 x

(<<<*>) :: (Applicative f, Applicative g, Applicative h)
        => f (g (h (a -> b))) -> f a -> f (g (h b))
h <<<*> x =
  getCompose2 $ Compose2 h <*> Compose2 (pure <$> (pure <$> x))

(<*<*>) :: forall a b f g h. (Applicative f, Applicative g, Applicative h)
        => f (g (h (a -> b))) -> f (h a) -> f (g (h b))
j <*<*> x = getCompose2 $ Compose2 j <*> Compose2 (pure <$> x)

-- ** Miscellaneous

-- | You can pull a functor out of a tuple if its an applicative
tupleA2 :: Applicative f => (f a, f b) -> f (a, b)
tupleA2 (f, s) = (,) <$> f <*> s

tupleA3 :: Applicative f => (f a, f b, f c) -> f (a, b, c)
tupleA3 (f, s, t) = (,,) <$> f <*> s <*> t

-- | Commute an applicative with Maybe
commuteMaybe :: Applicative f => Maybe (f a) -> f (Maybe a)
commuteMaybe (Just val) = Just <$> val
commuteMaybe Nothing    = pure Nothing
