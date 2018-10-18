{-# LANGUAGE FlexibleContexts #-}
{-|
Module      : Data.LLVM.BitCode.IR.Metadata.Resolve
Description : Resolve forward references in metadata blocks
Copyright   : (c) Galois, Inc 2018
License     : BSD-3
Maintainer  : atomb@galois.com
Stability   : experimental
-}

module Data.LLVM.BitCode.IR.Metadata.Resolve where

import           Text.LLVM.AST

import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Text (Text)
import           MonadLib

import           Data.LLVM.BitCode.Parse
import           Data.LLVM.BitCode.IR.Metadata.MetadataTable

resolveForwardRef :: ( WriterM m [Int]                -- Logging
                     , ReaderM m (PartialMetadata m)  -- Reading the unresolved table
                     , StateM m MetadataTable         -- R/W to the resolved table
                     , ExceptionM m ()                -- Resolution failure
                     )
                  => Int              -- ^ Index to resolve
                  -> m (Typed PValue) -- ^ Result
resolveForwardRef i = do
  puts i    -- Record that we're attempting to resolve this reference
  mt <- get -- Get what we've resolved so far
  case Map.lookup i mt of
    Just x  -> pure x -- We've already resolved this reference
    Nothing -> do
      _
