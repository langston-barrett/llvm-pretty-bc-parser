{-# LANGUAGE ViewPatterns #-}
module Data.LLVM.BitCode.IR.Metadata.Preparse where

import           Data.LLVM.BitCode.Bitstream
import           Data.LLVM.BitCode.IR.Blocks
import           Data.LLVM.BitCode.Match
import           Data.LLVM.BitCode.Parse
import           Data.LLVM.BitCode.Record
import           Text.LLVM.AST

import           Control.Arrow ((>>>))
import           Control.Monad ((>=>))
import           Data.Maybe (mapMaybe)
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.List as List

import           Data.LLVM.BitCode.IR.Metadata.Applicative
import           Data.LLVM.BitCode.IR.Metadata.Parse
import           Data.LLVM.BitCode.IR.Metadata.Table

-- | Returns a map from metadata IDs to the 'Record's that hold their
-- definition.
--
-- The keys of the map are @[0...n]@ for some @n@.
preparseMetadata :: [Entry] -> Map Int Record
preparseMetadata ents =
    -- First, we jump into any entries that contain metadata blocks.
    let fnMatch = functionBlockId
                  >=> mapM (metadataBlockId ||| metadataAttachmentBlockId)
                  >>> fmap concat
        mdEntries = concat $  mapMaybe metadataBlockId ents
                           ++ mapMaybe fnMatch         ents
    in -- We number these sequentially. Unnamed metadata nodes have implicit,
       -- incrementing IDs.
       Map.fromList $
         zip [0..] (filter isUnnamedMdRecord $ mapMaybe fromEntry mdEntries)
  where -- Is this a record containing implicitly named metadata?
        isUnnamedMdRecord :: Record -> Bool
        isUnnamedMdRecord = (`List.elem` [2, 3, 5, 8, 9]) . recordCode

-- Take the metadata records, parse them, and resolve all references between
-- them.
resolveMetadata :: Map Int Record -> Parse (Map Int PValMd)
resolveMetadata = helper []
  where helper :: [Int]          -- References we're resolving
               -> Map Int PValMd -- Done already
               -> Map Int Record -- Yet to be done
               -> Parse (Map Int PValMd)
        helper lst done todo = do

parseEntry :: ValueTable -> MetadataTable -> PartialMetadata -> Entry
           -> Parse PartialMetadata
parseEntry vt mt pm (fromEntry -> Just r) =
 case recordCode r of
  -- [values]
  1 -> label "METADATA_STRING" $ do
    str <- fmap UTF8.decode (parseFields r 0 char) `mplus` parseField r 0 string
    return $! updateMetadataTable (addString str) pm

  -- [type num, value num]
  2 -> label "METADATA_VALUE" $ do
    unless (length (recordFields r) == 2)
           (fail "Invalid record")

    let field = parseField r
    ty  <- getType =<< field 0 numeric
    when (ty == PrimType Metadata || ty == PrimType Void)
         (fail "invalid record")

    cxt <- getContext
    ix  <- field 1 numeric
    let tv = forwardRef cxt ix vt

    return $! updateMetadataTable (addMdValue tv) pm


  -- [n x md num]
  3 -> label "METADATA_NODE" (parseMetadataNode False mt r pm)

  -- [n x md num]
  5 -> label "METADATA_DISTINCT_NODE" (parseMetadataNode True mt r pm)
