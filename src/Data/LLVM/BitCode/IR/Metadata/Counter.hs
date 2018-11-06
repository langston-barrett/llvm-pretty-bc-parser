{-# LANGUAGE OverloadedStrings #-}
{-|
Module      : Data.LLVM.BitCode.IR.Metadata.Resolve
Description : Track progress of tasks
Copyright   : (c) Galois, Inc 2018
License     : BSD-3
Maintainer  : atomb@galois.com
Stability   : experimental
-}
module Data.LLVM.BitCode.IR.Metadata.Counter where

import qualified Data.Text as Text
import           Data.Text (Text)

-- | A 'Counter' holds two counts: progress so far, and the desired total.
newtype Counter = Counter { getCounter :: (Int, Int) }
  deriving Show

initCtr :: Int -> Counter
initCtr i = Counter (0, i)

zeroCtr :: Counter
zeroCtr = initCtr 0

incCtr :: Counter -> Counter
incCtr (Counter (soFar, total)) = Counter (soFar + 1, total)

-- setCtr :: (Int, Int) -> Counter -> Counter
-- setCtr (a, b) _ = Counter (a, b)

ppCtr :: Counter -> Text
ppCtr (Counter (soFar, total)) =
  Text.concat ["(", ts soFar, ", ", ts total, ")"]
  where ts = Text.pack . show
