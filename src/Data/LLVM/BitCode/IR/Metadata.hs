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

import Control.Monad (foldM)

import Data.LLVM.BitCode.Bitstream (Entry)
import Data.LLVM.BitCode.Parse

import Data.LLVM.BitCode.IR.Metadata.Parse
import Data.LLVM.BitCode.IR.Metadata.MetadataTable

-- | This is the entrypoint parsing a metadata block, it is called from e.g.
-- 'parseModule'.
parseMetadataBlock :: Int     -- ^ Globals seen so far
                   -> [Entry] -- ^ Entries in this LLVM module
                   -> Parse ParsedMetadata
parseMetadataBlock globals es = label "METADATA_BLOCK" $ do
  ms <- getMdTable
  let foldM' accum0 lst f = foldM f accum0 lst -- like "forM"
  pm <- foldM' (emptyPartialMetadata globals ms) es $ \pm e -> do
          vt <- getValueTable
          parseMetadataEntry vt pm e
  setMdTable $ mtEntries (pmEntries pm)
  setMdRefs (mkMdRefTable (pmEntries pm))
  pure $ parsedMetadata pm
