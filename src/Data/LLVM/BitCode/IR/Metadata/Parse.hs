{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

{-|
Module      : Data.LLVM.BitCode.IR.Metadata.Parse
Description : Parsing metadata blocks with unresolved forward references
Copyright   : (c) Galois, Inc 2018
License     : BSD-3
Maintainer  : atomb@galois.com
Stability   : experimental

Processing metadata blocks happens in two phases. In the first, the block is
parsed and forward references are recorded, but left unresolved. In the second,
the forward references are recursively resolved
(see "Data.LLVM.BitCode.IR.Metadata.Resolve").
-}

module Data.LLVM.BitCode.IR.Metadata.Parse where

import Data.LLVM.BitCode.Bitstream
import Data.LLVM.BitCode.Match
import Data.LLVM.BitCode.Parse
import Data.LLVM.BitCode.Record
import Text.LLVM.AST
import Text.LLVM.Labels

import qualified Codec.Binary.UTF8.String as UTF8 (decode)
import           MonadLib (ReaderM, ExceptionM, ask, raise)
import           Control.Monad (foldM,guard,mplus,unless,when)
import qualified Control.Exception as X (throw)
import           Data.List (mapAccumL)
import           Data.Maybe (fromMaybe)
import           Data.Bits (shiftR, testBit, shiftL)
import           Data.Word (Word32,Word64)
import qualified Data.ByteString as S
import qualified Data.ByteString.Char8 as Char8 (unpack)
import qualified Data.Map as Map

import Data.LLVM.BitCode.IR.Metadata.MetadataTable

import Debug.Trace
import Data.Functor.Compose

-- Metadata Parsing ------------------------------------------------------------

-- | Parse an entry in the metadata block.
--
-- XXX this currently relies on the constant block having been parsed already.
-- Though most bitcode examples I've seen are ordered this way, it would be nice
-- to not have to rely on it.
parseMetadataEntry :: forall m. Applicative m
                   => ValueTable        -- ^ The current value table
                   -> MetadataTable     -- ^ The current metadata table (can be empty)
                   -> PartialMetadata m -- ^ Metadata processed so far
                   -> Entry             -- ^ The entry to be processed
                   -> Parse (PartialMetadata m)
parseMetadataEntry vt mt pm (fromEntry -> Just r) =
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
    tv  <- forwardRef cxt ix vt

    return $! updateMetadataTable (addMdValue tv) pm


  -- [n x md num]
  3 -> label "METADATA_NODE" (parseMetadataNode False mt r pm)

  -- [values]
  4 -> label "METADATA_NAME" $ do
    name <- fmap UTF8.decode (parseFields r 0 char) `mplus` parseField r 0 cstring
    return $! setNextName name pm

  -- [n x md num]
  5 -> label "METADATA_DISTINCT_NODE" (parseMetadataNode True mt r pm)

  -- [n x [id, name]]
  6 -> label "METADATA_KIND" $ do
    kind <- parseField r 0 numeric
    name <- UTF8.decode <$> parseFields r 1 char
    addKind kind name
    return pm

  -- [distinct, line, col, scope, inlined-at?]
  7 -> label "METADATA_LOCATION" $ do
    -- TODO: broken in 3.7+; needs to be a DILocation rather than an
    -- MDLocation, but there appears to be no difference in the
    -- bitcode. /sigh/
    cxt       <- getContext
    let field = parseField r
    isDistinct <- field 0 nonzero
    dlLine     <- field 1 numeric
    dlCol      <- field 2 numeric
    dlScope    <- mdForwardRef mt       <$> field 3 numeric
    dlIA       <- mdForwardRefOrNull mt <$> field 4 numeric
    let mkLoc dlScope dlIA = DebugLoc { .. }
    let loc = mkLoc <$> dlScope <*> commuteMaybe dlIA
    return $! updateMetadataTable (addLoc' isDistinct loc) pm
    where -- | Commute an applicative with Maybe
          commuteMaybe :: Applicative n => Maybe (n a) -> n (Maybe a)
          commuteMaybe (Just val) = Just <$> val
          commuteMaybe Nothing    = pure Nothing

  -- [n x (type num, value num)]
  8 -> label "METADATA_OLD_NODE" (parseMetadataOldNode False vt mt r pm)

  -- [n x (type num, value num)]
  9 -> label "METADATA_OLD_FN_NODE" (parseMetadataOldNode True vt mt r pm)

  -- [n x mdnodes]
  10 -> label "METADATA_NAMED_NODE" $ do
    mdIds <- parseFields r 0 numeric
    cxt   <- getContext
    case mapM (mdNodeRef mt) mdIds of
      Just ids -> nameMetadata ids pm
      Nothing  -> fail $ unwords $ [ "References to metadata nodes failed: "
                                   , show mdIds
                                   ]

  -- [m x [value, [n x [id, mdnode]]]
  11 -> label "METADATA_ATTACHMENT" $ do
    let recordSize = length (recordFields r)
    when (recordSize == 0)
      (fail "Invalid record")
    if recordSize `mod` 2 == 0
      then label "function attachment" $ do
        att <- Map.fromList <$> parseAttachment r 0
        return $! addFnAttachment att pm
      else label "instruction attachment" $ do
        inst <- parseField r 0 numeric
        patt <- parseAttachment r 1
        att  <- mapM (\(k,md) -> (,md) <$> getKind k) patt
        return $! addInstrAttachment inst att pm

  12 -> label "METADATA_GENERIC_DEBUG" $
    --isDistinct <- parseField r 0 numeric
    --tag <- parseField r 1 numeric
    --version <- parseField r 2 numeric
    --header <- parseField r 3 string
    -- TODO: parse all remaining fields
    fail "not yet implemented"

  13 -> label "METADATA_SUBRANGE" $ do
    isDistinct     <- parseField r 0 nonzero
    disrCount      <- parseField r 1 numeric
    disrLowerBound <- parseField r 2 signedInt64
    return $! updateMetadataTable
      (addDebugInfo' isDistinct (DebugInfoSubrange DISubrange{..})) pm

  -- [distinct, value, name]
  14 -> label "METADATA_ENUMERATOR" $ do
    ctx        <- getContext
    isDistinct <- parseField r 0 nonzero
    value      <- parseField r 1 signedInt64
    name       <- mdString mt <$> parseField r 2 numeric
    return $! updateMetadataTable
      (addDebugInfo' isDistinct (DebugInfoEnumerator <$> name <*> pure value)) pm

  15 -> label "METADATA_BASIC_TYPE" $ do
    ctx <- getContext
    isDistinct   <- parseField r 0 nonzero
    dibtTag      <- parseField r 1 numeric
    dibtName'    <- mdString mt <$> parseField r 2 numeric
    dibtSize     <- parseField r 3 numeric
    dibtAlign    <- parseField r 4 numeric
    dibtEncoding <- parseField r 5 numeric
    let diBasicType = {- Get under the forward reference monad -}
          (\dibtName -> DebugInfoBasicType DIBasicType{..})
          <$> dibtName'
    return $! updateMetadataTable
      (addDebugInfo' isDistinct diBasicType) pm

  -- [distinct, filename, directory]
  16 -> label "METADATA_FILE" $ do
--     ctx <- getContext
--     isDistinct <- parseField r 0 nonzero
--     difFilename <- mdString ctx mt <$> parseField r 1 numeric
--     difDirectory <- mdString ctx mt <$> parseField r 2 numeric
--     return $! updateMetadataTable
-- (addDebugInfo isDistinct (DebugInfoFile DIFile{..})) pmDATA_FILE" $ do
    ctx           <- getContext
    isDistinct    <- parseField r 0 nonzero
    difFilename'  <- mdString mt <$> parseField r 1 numeric
    difDirectory' <- mdString mt <$> parseField r 2 numeric
    let diFile :: WithForwardMdRef m => Compose m Parse DIFile
        diFile =
          DIFile
            <$$> (mdString mt <$> parseField r 1 numeric) -- name
            <**> _
            <**> _
          where f <$$> x = f <$> Compose x
                x <**> y = x <*> Compose y
    return $! updateMetadataTable
      (addDebugInfo' isDistinct diFile) pm

  17 -> label "METADATA_DERIVED_TYPE" $ do
    ctx <- getContext
    isDistinct    <- parseField r 0 nonzero
    -- let diDerivedType :: WithForwardMdRef m => Compose m Parse _
    --     diDerivedType = DIDerivedType
    --       <$> (Compose (pure $ parseField r 1 numeric))
    --       <$> (mdStringOrNull     mt <$> parseField r 2 numeric) -- didtName
    --       <$> _
    --       <$> _
    --       <$> _
    --       <$> _
    --       <$> _
    --       <$> _
    --       <$> _
    --       <$> _
    --       where (<$$>) = fmap . fmap
    let
        diDerivedType = DIDerivedType
          <$> (pure $ parseField r 1 numeric)                             -- didtTag
          <$> (mdStringOrNull     mt <$> parseField r 2 numeric) -- didtName
          <$> (mdForwardRefOrNull mt <$> parseField r 3 numeric) -- didtFile
          <$> (pure $ parseField r 4 numeric)                             -- didtLine
          <$> (mdForwardRefOrNull mt <$> parseField r 5 numeric) -- didtScope
          <$> (mdForwardRefOrNull mt <$> parseField r 6 numeric) -- didtBaseType
          <$> (pure $ parseField r 7 numeric)                             -- didtSize
          <$> (pure $ parseField r 8 numeric)                             -- didtAlign
          <$> (pure $ parseField r 9 numeric)                             -- didtOffset
          <$> (pure $ parseField r 10 numeric)                            -- didtFlags
          <$> (mdForwardRefOrNull mt <$> parseField r 11 numeric) -- didtExtraData
          where (<$$>) = fmap . fmap
    -- let diFile = {- Get under the forward reference monad -}
    --       (\difFilename difDirectory -> DebugInfoBasicType DIBasicType{..})
    --       <$> difFilename'
    --       <*> difDirectory'
    return $! updateMetadataTable
      (addDebugInfo isDistinct (DebugInfoDerivedType DIDerivedType{..})) pm

  18 -> label "METADATA_COMPOSITE_TYPE" $ do
    ctx <- getContext
    isDistinct         <- parseField r 0 nonzero
    dictTag            <- parseField r 1 numeric
    dictName           <- mdStringOrNull     ctx mt =<< parseField r 2 numeric
    dictFile           <- mdForwardRefOrNull mt <$> parseField r 3 numeric
    dictLine           <- parseField r 4 numeric
    dictScope          <- mdForwardRefOrNull mt <$> parseField r 5 numeric
    dictBaseType       <- mdForwardRefOrNull mt <$> parseField r 6 numeric
    dictSize           <- parseField r 7 numeric
    dictAlign          <- parseField r 8 numeric
    dictOffset         <- parseField r 9 numeric
    dictFlags          <- parseField r 10 numeric
    dictElements       <- mdForwardRefOrNull mt <$> parseField r 11 numeric
    dictRuntimeLang    <- parseField r 12 numeric
    dictVTableHolder   <- mdForwardRefOrNull mt <$> parseField r 13 numeric
    dictTemplateParams <- mdForwardRefOrNull mt <$> parseField r 14 numeric
    dictIdentifier     <- mdStringOrNull     ctx mt =<< parseField r 15 numeric
    return $! updateMetadataTable
      (addDebugInfo isDistinct (DebugInfoCompositeType DICompositeType{..})) pm

  19 -> label "METADATA_SUBROUTINE_TYPE" $ do
    ctx <- getContext
    isDistinct    <- parseField r 0 nonzero
    distFlags     <- parseField r 1 numeric
    distTypeArray <- mdForwardRefOrNull mt <$> parseField r 2 numeric
    return $! updateMetadataTable
      (addDebugInfo
         isDistinct
         (DebugInfoSubroutineType DISubroutineType{..}))
      pm

  20 -> label "METADATA_COMPILE_UNIT" $ do
    let recordSize = length (recordFields r)

    when (recordSize < 14 || recordSize > 19)
      (fail "Invalid record")

    ctx <- getContext
    isDistinct             <- parseField r 0 nonzero
    dicuLanguage           <- parseField r 1 numeric
    dicuFile               <-
      mdForwardRefOrNull mt <$> parseField r 2 numeric
    dicuProducer           <- mdStringOrNull ctx mt =<< parseField r 3 numeric
    dicuIsOptimized        <- parseField r 4 nonzero
    dicuFlags              <- mdStringOrNull ctx mt =<< parseField r 5 numeric
    dicuRuntimeVersion     <- parseField r 6 numeric
    dicuSplitDebugFilename <- mdStringOrNull ctx mt =<< parseField r 7 numeric
    dicuEmissionKind       <- parseField r 8 numeric
    dicuEnums              <-
      mdForwardRefOrNull mt <$> parseField r 9 numeric
    dicuRetainedTypes      <-
      mdForwardRefOrNull mt <$> parseField r 10 numeric
    dicuSubprograms        <-
      mdForwardRefOrNull mt <$> parseField r 11 numeric
    dicuGlobals            <-
      mdForwardRefOrNull mt <$> parseField r 12 numeric
    dicuImports            <-
      mdForwardRefOrNull mt <$> parseField r 13 numeric
    dicuMacros <-
      if recordSize <= 15
      then pure Nothing
      else mdForwardRefOrNull mt <$> parseField r 15 numeric
    dicuDWOId <-
      if recordSize <= 14
      then pure 0
      else parseField r 14 numeric
    dicuSplitDebugInlining <-
      if recordSize <= 16
      then pure True
      else parseField r 16 nonzero
    return $! updateMetadataTable
      (addDebugInfo isDistinct (DebugInfoCompileUnit DICompileUnit {..})) pm


  21 -> label "METADATA_SUBPROGRAM" $ do
    -- this one is a bit funky:
    -- https://github.com/llvm-mirror/llvm/blob/release_50/lib/Bitcode/Reader/MetadataLoader.cpp#L1382
    let recordSize = length (recordFields r)
        adj i | recordSize == 19 = i + 1
              | otherwise        = i
        hasThisAdjustment = recordSize >= 20
        hasThrownTypes = recordSize >= 21
    unless (18 <= recordSize && recordSize <= 21)
      (fail ("Invalid subprogram record, size = " ++ show recordSize))

    ctx <- getContext
    isDistinct         <- parseField r 0 nonzero
    dispScope          <- mdForwardRefOrNull mt <$> parseField r 1 numeric
    dispName           <- mdStringOrNull ctx mt =<< parseField r 2 numeric
    dispLinkageName    <- mdStringOrNull ctx mt =<< parseField r 3 numeric
    dispFile           <- mdForwardRefOrNull mt <$> parseField r 4 numeric
    dispLine           <- parseField r 5 numeric
    dispType           <- mdForwardRefOrNull mt <$> parseField r 6 numeric
    dispIsLocal        <- parseField r 7 nonzero
    dispIsDefinition   <- parseField r 8 nonzero
    dispScopeLine      <- parseField r 9 numeric
    dispContainingType <- mdForwardRefOrNull mt <$> parseField r 10 numeric
    dispVirtuality     <- parseField r 11 numeric
    dispVirtualIndex   <- parseField r 12 numeric
    dispThisAdjustment <- if hasThisAdjustment
                            then parseField r 19 numeric
                            else return 0
    dispThrownTypes <- if hasThrownTypes
                         then mdForwardRefOrNull mt <$> parseField r 20 numeric
                         else return Nothing
    dispFlags          <- parseField r 13 numeric
    dispIsOptimized    <- parseField r 14 nonzero
    dispTemplateParams <-
      mdForwardRefOrNull mt <$> parseField r (adj 15) numeric
    dispDeclaration <-
      mdForwardRefOrNull mt <$> parseField r (adj 16) numeric
    dispVariables <-
      mdForwardRefOrNull mt <$> parseField r (adj 17) numeric
    -- TODO: in the LLVM parser, it then goes into the metadata table
    -- and updates function entries to point to subprograms. Is that
    -- neccessary for us?
    return $! updateMetadataTable
      (addDebugInfo isDistinct (DebugInfoSubprogram DISubprogram{..})) pm

  22 -> label "METADATA_LEXICAL_BLOCK" $ do
    when (length (recordFields r) /= 5)
      (fail "Invalid record")
    cxt <- getContext
    isDistinct <- parseField r 0 nonzero
    dilbScope  <- mdForwardRefOrNull cxt mt =<< parseField r 1 numeric
    dilbFile   <- mdForwardRefOrNull cxt mt =<< parseField r 2 numeric
    dilbLine   <- parseField r 3 numeric
    dilbColumn <- parseField r 4 numeric
    return $! updateMetadataTable
      (addDebugInfo isDistinct (DebugInfoLexicalBlock DILexicalBlock{..})) pm

  23 -> label "METADATA_LEXICAL_BLOCK_FILE" $ do
    when (length (recordFields r) /= 4)
      (fail "Invalid record")
    cxt <- getContext
    isDistinct <- parseField r 0 nonzero
    dilbfScope <- do
      mScope <- mdForwardRefOrNull cxt mt =<< parseField r 1 numeric
      maybe (fail "Invalid record: scope field not present") return mScope
    dilbfFile <- mdForwardRefOrNull cxt mt =<< parseField r 2 numeric
    dilbfDiscriminator <- parseField r 3 numeric
    return $! updateMetadataTable
      (addDebugInfo
         isDistinct
         (DebugInfoLexicalBlockFile DILexicalBlockFile{..}))
      pm

  24 -> label "METADATA_NAMESPACE" $ do
    isNew <- case length (recordFields r) of
               3 -> return True
               5 -> return False
               _ -> fail "Invalid METADATA_NAMESPACE record"
    cxt <- getContext
    isDistinct <- parseField r 0 nonzero
    dinsScope <- mdForwardRef cxt mt =<< parseField r 1 numeric
    dinsFile <- if isNew
                then return (ValMdString "")
                else mdForwardRef cxt mt =<< parseField r 2 numeric
    let nameIdx = if isNew then 2 else 3
    dinsName <- mdString cxt mt =<< parseField r nameIdx numeric
    dinsLine <- if isNew then return 0 else parseField r 4 numeric
    return $! updateMetadataTable
        (addDebugInfo
            isDistinct
            (DebugInfoNameSpace DINameSpace{..}))
        pm
  25 -> label "METADATA_TEMPLATE_TYPE" $ do
    cxt <- getContext
    isDistinct <- parseField r 0 nonzero
    dittpName <- mdString cxt mt =<< parseField r 1 numeric
    dittpType <- mdForwardRef cxt mt =<< parseField r 2 numeric
    return $! updateMetadataTable
            (addDebugInfo
                isDistinct
                (DebugInfoTemplateTypeParameter DITemplateTypeParameter{..}))
            pm
  26 -> label "METADATA_TEMPLATE_VALUE" $ do
    cxt <- getContext
    isDistinct <- parseField r 0 nonzero
    ditvpName  <- mdString cxt mt =<< parseField r 1 numeric
    ditvpType  <- mdForwardRef cxt mt =<< parseField r 2 numeric
    ditvpValue <- mdForwardRef cxt mt =<< parseField r 3 numeric
    return $! updateMetadataTable
            (addDebugInfo
                isDistinct
                (DebugInfoTemplateValueParameter DITemplateValueParameter{..}))
            pm

  27 -> label "METADATA_GLOBAL_VAR" $ do
    let len = length (recordFields r)
    unless (11 <= len && len <= 12)
      (fail "Unexpected number of record fields")

    ctx        <- getContext
    field0     <- parseField r 0 numeric
    let isDistinct = testBit field0 0
        _version   = shiftR  field0 1 :: Int

    digvScope  <- mdForwardRefOrNull mt <$> parseField r 1 numeric
    digvName   <- mdStringOrNull ctx mt =<< parseField r 2 numeric
    digvLinkageName <- mdStringOrNull ctx mt =<< parseField r 3 numeric
    digvFile   <- mdForwardRefOrNull mt <$> parseField r 4 numeric
    digvLine   <- parseField r 5 numeric
    digvType   <- mdForwardRefOrNull mt <$> parseField r 6 numeric
    digvIsLocal <- parseField r 7 nonzero
    digvIsDefinition <- parseField r 8 nonzero
    digvVariable <- mdForwardRefOrNull mt <$> parseField r 9 numeric
    digvDeclaration <- mdForwardRefOrNull mt <$> parseField r 10 numeric
    digvAlignment   <- if len > 11 then Just <$> parseField r 11 numeric
                                   else return Nothing
    return $! updateMetadataTable
      (addDebugInfo
         isDistinct
         (DebugInfoGlobalVariable DIGlobalVariable{..})) pm

  28 -> label "METADATA_LOCAL_VAR" $ do
    -- this one is a bit funky:
    -- https://github.com/llvm-mirror/llvm/blob/release_38/lib/Bitcode/Reader/BitcodeReader.cpp#L2308
    let recordSize = length (recordFields r)
    when (recordSize < 8 || recordSize > 10)
      (fail "Invalid record")

    ctx <- getContext

    field0 <- parseField r 0 numeric
    let isDistinct   = testBit (field0 :: Word32) 0
        hasAlignment = testBit (field0 :: Word32) 1

        hasTag | not hasAlignment && recordSize > 8 = 1
               | otherwise                          = 0

        adj i = i + hasTag

    _alignInBits <-
      if hasAlignment
         then do n <- parseField r (adj 8) numeric
                 when ((n :: Word64) > fromIntegral (maxBound :: Word32))
                      (fail "Alignment value is too large")
                 return (fromIntegral n :: Word32)

         else return 0

    dilvScope  <- mdForwardRefOrNull ("dilvScope":ctx) mt =<< parseField r (adj 1) numeric
    dilvName   <- mdStringOrNull     ("dilvName" :ctx) mt =<< parseField r (adj 2) numeric
    dilvFile   <- mdForwardRefOrNull ("dilvFile" :ctx) mt =<< parseField r (adj 3) numeric
    dilvLine   <- parseField r (adj 4) numeric
    dilvType   <- mdForwardRefOrNull ("dilvType" :ctx) mt =<< parseField r (adj 5) numeric
    dilvArg    <- parseField r (adj 6) numeric
    dilvFlags  <- parseField r (adj 7) numeric
    return $! updateMetadataTable
      (addDebugInfo isDistinct (DebugInfoLocalVariable DILocalVariable{..})) pm

  29 -> label "METADATA_EXPRESSION" $ do
    let recordSize = length (recordFields r)
    when (recordSize < 1)
      (fail "Invalid record")
    isDistinct <- parseField r 0 nonzero
    dieElements <- parseFields r 1 numeric
    return $! updateMetadataTable
      (addDebugInfo isDistinct (DebugInfoExpression DIExpression{..})) pm

  30 -> label "METADATA_OBJC_PROPERTY" $
    -- TODO
    fail "not yet implemented"
  31 -> label "METADATA_IMPORTED_ENTITY" $ do
    cxt <- getContext
    isDistinct <- parseField r 0 nonzero
    diieTag    <- parseField r 1 numeric
    diieScope  <- mdForwardRefOrNull cxt mt =<< parseField r 2 numeric
    diieEntity <- mdForwardRefOrNull cxt mt =<< parseField r 3 numeric
    diieLine   <- parseField r 4 numeric
    diieName   <- mdString cxt mt =<< parseField r 5 numeric
    return $! updateMetadataTable
        (addDebugInfo
            isDistinct
            (DebugInfoImportedEntity DIImportedEntity{..}))
        pm
  32 -> label "METADATA_MODULE" $
    -- cxt <- getContext
    -- isDistinct <- parseField r 0 numeric
    -- mdForwardRefOrNull cxt mt =<< parseField r 1 numeric
    -- parseField r 2 string
    -- parseField r 3 string
    -- parseField r 4 string
    -- parseField r 5 string
    -- TODO
    fail "not yet implemented"
  33 -> label "METADATA_MACRO" $
    -- isDistinct <- parseField r 0 numeric
    -- parseField r 1 numeric
    -- parseField r 2 numeric
    -- parseField r 3 string
    -- parseField r 4 string
    -- TODO
    fail "not yet implemented"
  34 -> label "METADATA_MACRO_FILE" $
    -- cxt <- getContext
    -- isDistinct <- parseField r 0 numeric
    -- parseField r 1 numeric
    -- parseField r 2 numeric
    -- mdForwardRefOrNull cxt mt =<< parseField r 3 numeric
    -- mdForwardRefOrNull cxt mt =<< parseField r 4 numeric
    -- TODO
    fail "not yet implemented"

  35 -> label "METADATA_STRINGS" $ do
    when (length (recordFields r) /= 3)
      (fail "Invalid record: metadata strings layout")
    count  <- parseField r 0 numeric
    offset <- parseField r 1 numeric
    bs     <- parseField r 2 fieldBlob
    when (count == 0)
      (fail "Invalid record: metadata strings with no strings")
    when (offset >= S.length bs)
      (fail "Invalid record: metadata strings corrupt offset")
    let (bsLengths, bsStrings) = S.splitAt offset bs
    lengths <- either fail return $ parseMetadataStringLengths count bsLengths
    when (sum lengths > S.length bsStrings)
      (fail "Invalid record: metadata strings truncated")
    let strings = snd (mapAccumL f bsStrings lengths)
          where f s i = case S.splitAt i s of
                          (str,rest) -> (rest, Char8.unpack str)
    return $! updateMetadataTable (addStrings strings) pm

  -- [ valueid, n x [id, mdnode] ]
  36 -> label "METADATA_GLOBAL_DECL_ATTACHMENT" $ do

    -- the record will always be of odd length
    when (mod (length (recordFields r)) 2 == 0)
         (fail "Invalid record")

    valueId <- parseField r 0 numeric
    sym     <- case lookupValueTableAbs valueId vt of
                 Just Typed{ typedValue = ValSymbol sym } -> return sym
                 _ -> fail "Non-global referenced"

    refs <- parseGlobalObjectAttachment mt r

    return $! addGlobalAttachments sym refs pm

  37 -> label "METADATA_GLOBAL_VAR_EXPR" $ do
    when (length (recordFields r) /= 3)
      (fail "Invalid record: unsupported layout")
    cxt <- getContext
    isDistinct      <- parseField r 0 nonzero
    digveVariable   <- mdForwardRefOrNull cxt mt =<< parseField r 1 numeric
    digveExpression <- mdForwardRefOrNull cxt mt =<< parseField r 2 numeric
    return $! updateMetadataTable
      (addDebugInfo isDistinct (DebugInfoGlobalVariableExpression DIGlobalVariableExpression{..})) pm

  38 -> label "METADATA_INDEX_OFFSET" $ do

    when (length (recordFields r) /= 2)
         (fail "Invalid record")

    a <- parseField r 0 numeric
    b <- parseField r 1 numeric
    let _offset = a + (b `shiftL` 32) :: Word64

    -- TODO: is it OK to skip this if we always parse everything?
    return pm


  -- In the llvm source, this node is processed when the INDEX_OFFSET record is
  -- found.
  39 -> label "METADATA_INDEX" $
    -- TODO: is it OK to skip this if we always parse everything?
    return pm

  code -> fail ("unknown record code: " ++ show code)

parseMetadataEntry _ _ pm (abbrevDef -> Just _) =
  return pm

parseMetadataEntry _ _ _ r =
  fail ("unexpected metadata entry: " ++ show r)

parseAttachment :: Record -> Int -> Parse [(PKindMd,PValMd)]
parseAttachment r l = loop (length (recordFields r) - 1) []
  where
  loop n acc | n < l = return acc
             | otherwise = do
    kind <- parseField r (n - 1) numeric
    md   <- getMetadata =<< parseField r n numeric
    loop (n - 2) ((kind,typedValue md) : acc)


-- | This is a named version of the metadata list that can show up at the end of
-- a global declaration. It will be of the form @!dbg !2 [!dbg !n, ...]@.
parseGlobalObjectAttachment :: MetadataTable -> Record -> Parse (Map.Map KindMd PValMd)
parseGlobalObjectAttachment mt r = label "parseGlobalObjectAttachment" $
  do cxt <- getContext
     go cxt Map.empty 1
  where
  len = length (recordFields r)

  go cxt acc n | n < len =
    do kind <- getKind =<< parseField r n numeric
       i    <- parseField r (n + 1) numeric
       ref  <- mdForwardRef cxt mt i
       go cxt (Map.insert kind ref acc) (n + 2)

  go _ acc _ =
       return acc


-- | Parse a metadata node.
parseMetadataNode :: Bool -> MetadataTable
                  -> Record -> PartialMetadata m
                  -> Parse (PartialMetadata m)
parseMetadataNode isDistinct mt r pm = trace "parseMetadataNode" $ do
  ixs <- parseFields r 0 numeric
  cxt <- getContext
  mt  <- _
  let lkp = traverse (mdForwardRefOrNull mt) ixs
  return $! updateMetadataTable (addNodeF isDistinct lkp) pm
  where -- | Commute an applicative with Maybe
        commuteMaybe :: Applicative n => Maybe (n a) -> n (Maybe a)
        commuteMaybe (Just val) = Just <$> val
        commuteMaybe Nothing    = pure Nothing


-- | Parse out a metadata node in the old format.
parseMetadataOldNode :: Bool -> ValueTable -> MetadataTable -> Record
                     -> PartialMetadata m -> Parse (PartialMetadata m)
parseMetadataOldNode fnLocal vt mt r pm = do
  values <- loop =<< parseFields r 0 numeric
  return $! updateMetadataTable (addOldNode fnLocal values) pm
  where
  loop :: [Int] -> Parse [Typed PValue]
  loop fs = case fs of

    tyId:valId:rest -> do
      cxt <- getContext
      ty  <- getType' tyId
      val <- case ty of
        PrimType Metadata ->
          Typed (PrimType Metadata) . ValMd <$> mdForwardRef cxt mt valId
        -- XXX need to check for a void type here
        _                 -> forwardRef cxt valId vt

      vals <- loop rest
      return (val:vals)

    [] -> return []

    _ -> fail "Malformed metadata node"

parseMetadataKindEntry :: Record -> Parse ()
parseMetadataKindEntry r = do
  kind <- parseField  r 0 numeric
  name <- parseFields r 1 char
  addKind kind (UTF8.decode name)
