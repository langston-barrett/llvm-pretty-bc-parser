{-|
Module      : Data.LLVM.BitCode.IR.Metadata
Description : Parsing metadata blocks
Copyright   : (c) Galois, Inc 2018
License     : BSD-3
Maintainer  : atomb@galois.com
Stability   : experimental
-}

module Data.LLVM.BitCode.IR.Metadata (
    parseMetadataBlock
  , parseMetadataKindEntry
  , PartialUnnamedMd(..)
  , finalizePartialUnnamedMd
  , finalizePValMd
  , InstrMdAttachments
  , PFnMdAttachments
  , PKindMd
  , PGlobalAttachments
  ) where

import           Control.Monad (foldM)
import qualified Data.Map as Map

import           Data.LLVM.BitCode.Bitstream (Entry)
import           Data.LLVM.BitCode.Parse

import           Data.LLVM.BitCode.IR.Metadata.Parse
import           Data.LLVM.BitCode.IR.Metadata.Table
import           Data.LLVM.BitCode.IR.Metadata.Resolve

-- | This is the entrypoint parsing a metadata block, it is called from e.g.
-- 'parseModule'.
parseMetadataBlock ::
  Int {- ^ globals seen so far -} ->
  ValueTable -> [Entry] -> Parse ParsedMetadata
parseMetadataBlock globals vt es = label "METADATA_BLOCK" $ do
  ms <- getMdTable
  let pm0 = emptyPartialMetadata globals ms
  pm <- foldM (parseMetadataEntry vt (emptyMetadataTable globals ms)) pm0 es
  let entries = pmEntries pm
  _
  -- setMdTable (mtEntries    entries)
  -- setMdRefs  (mkMdRefTable entries)
  -- return (parsedMetadata pm)
