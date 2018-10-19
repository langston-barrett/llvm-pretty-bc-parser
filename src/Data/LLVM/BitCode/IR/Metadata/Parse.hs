{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
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

import qualified Codec.Binary.UTF8.String as UTF8 (decode)
import Control.Monad (join, mplus, unless, when)
import Data.Functor.Compose (getCompose, Compose(..))
import Data.List (mapAccumL)
import Data.Bits (shiftR, testBit, shiftL)
import Data.Word (Word32,Word64)
import qualified Data.ByteString as S
import qualified Data.ByteString.Char8 as Char8 (unpack)
import qualified Data.Map as Map

import Data.LLVM.BitCode.IR.Metadata.Table
import Data.LLVM.BitCode.IR.Metadata.Applicative ((<$$>), (<$>>), (<<$>))
import Data.LLVM.BitCode.IR.Metadata.Applicative ((<**>), (<*>>), (<<*>))
import Data.LLVM.BitCode.IR.Metadata.Applicative (commuteMaybe)

-- Metadata Parsing ------------------------------------------------------------

-- | Parse an entry in the metadata block.
--
-- XXX this currently relies on the constant block having been parsed already.
-- Though most bitcode examples I've seen are ordered this way, it would be nice
-- to not have to rely on it.
parseMetadataEntry :: forall m. Applicative m
                   => ValueTable
                   -> MetadataTable
                   -> PartialMetadata m
                   -> Entry
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
    let tv = forwardRef cxt ix vt

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
    let field = parseField r
    cxt        <- getContext
    isDistinct <- field 0 nonzero
    loc'       <- (getCompose :: Compose Parse m w -> Parse (m w)) $ DebugLoc
      <<$> field 1 numeric                               -- dlLine
      <<*> field 2 numeric                               -- dlCol
      <**> (mdForwardRef       mt <$> field 3 numeric)   -- dlScope
      <**> (commuteMaybe <$>
            (mdForwardRefOrNull mt <$> field 4 numeric)) -- dlIA
    return $! updateMetadataTableA (addLoc isDistinct <$> loc') pm

  -- [n x (type num, value num)]
  8 -> label "METADATA_OLD_NODE" (parseMetadataOldNode False vt mt r pm)

  -- [n x (type num, value num)]
  9 -> label "METADATA_OLD_FN_NODE" (parseMetadataOldNode True vt mt r pm)

  -- [n x mdnodes]
  10 -> label "METADATA_NAMED_NODE" $ do
    mdIds <- parseFields r 0 numeric
    cxt   <- getContext
    let ids :: f [Int]
        ids = traverse (mdNodeRef cxt $ pure mt) mdIds
    join (nameMetadata <$> ids <*> pure pm)

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
      att <- mapM (\(k,md) -> (,md) <$> getKind k) patt
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
    diNode         <- DISubrange
      <$> parseField r 1 numeric     -- disrCount
      <*> parseField r 2 signedInt64 -- disrLowerBound
    return $! updateMetadataTable
      (addDebugInfo isDistinct (DebugInfoSubrange diNode)) pm

  -- [distinct, value, name]
  14 -> label "METADATA_ENUMERATOR" $ do
    ctx        <- getContext
    isDistinct <- parseField r 0 nonzero
    diEnum     <- (getCompose :: Compose Parse m w -> Parse (m w)) $
      flip DebugInfoEnumerator
        <<$> parseField r 1 signedInt64                   -- value
        <**> (mdString ctx mt <$> parseField r 2 numeric) -- name
    return $! updateMetadataTableA (addDebugInfo isDistinct <$> diEnum) pm

  15 -> label "METADATA_BASIC_TYPE" $ do
    ctx        <- getContext
    isDistinct <- parseField r 0 nonzero
    dibt       <- (getCompose :: Compose Parse m w -> Parse (m w)) $ DIBasicType
      <<$> parseField r 1 numeric                       -- dibtTag
      <**> (mdString ctx mt <$> parseField r 2 numeric) -- dibtName
      <<*> parseField r 3 numeric                       -- dibtSize
      <<*> parseField r 4 numeric                       -- dibtAlign
      <<*> parseField r 5 numeric                       -- dibtEncoding
    return $! updateMetadataTableA
      (addDebugInfo isDistinct <$> (DebugInfoBasicType <$> dibt)) pm

  -- [distinct, filename, directory]
  16 -> label "METADATA_FILE" $ do
    ctx        <- getContext
    isDistinct <- parseField r 0 nonzero
    diFile     <- (getCompose :: Compose Parse m w -> Parse (m w)) $ DIFile
      <$$> (mdString ctx mt <$> parseField r 1 numeric) -- difFilename
      <**> (mdString ctx mt <$> parseField r 2 numeric) -- difDirectory
    return $! updateMetadataTableA
      (addDebugInfo isDistinct <$> (DebugInfoFile <$> diFile)) pm

  17 -> label "METADATA_DERIVED_TYPE" $ do
    ctx        <- getContext
    isDistinct <- parseField r 0 nonzero
    didt       <- (getCompose :: Compose Parse m w -> Parse (m w)) $ DIDerivedType
      <<$> parseField r 1 numeric                                  -- didtTag
      <**> (mdStringOrNull     ctx mt <$> parseField r 2 numeric)  -- didtName
      <**> (mdForwardRefOrNull     mt <$> parseField r 3 numeric)  -- didtFile
      <<*> parseField r 4 numeric                                  -- didtLine
      <**> (mdForwardRefOrNull     mt <$> parseField r 5 numeric)  -- didtScope
      <**> (mdForwardRefOrNull     mt <$> parseField r 6 numeric)  -- didtBaseType
      <<*> parseField r 7 numeric                                  -- didtSize
      <<*> parseField r 8 numeric                                  -- didtAlign
      <<*> parseField r 9 numeric                                  -- didtOffset
      <<*> parseField r 10 numeric                                 -- didtFlags
      <**> (mdForwardRefOrNull     mt <$> parseField r 11 numeric) -- didtExtraData
    return $! updateMetadataTableA
      (addDebugInfo isDistinct <$> (DebugInfoDerivedType <$> didt)) pm

  18 -> label "METADATA_COMPOSITE_TYPE" $ do
    ctx        <- getContext
    isDistinct <- parseField r 0 nonzero
    dict       <- (getCompose :: Compose Parse m w -> Parse (m w)) $ DICompositeType
      <<$> parseField r 1 numeric                                  -- dictTag
      <**> (mdStringOrNull     ctx mt <$> parseField r 2 numeric)  -- dictName
      <**> (mdForwardRefOrNull     mt <$> parseField r 3 numeric)  -- dictFile
      <<*> parseField r 4 numeric                                  -- dictLine
      <**> (mdForwardRefOrNull     mt <$> parseField r 5 numeric)  -- dictScope
      <**> (mdForwardRefOrNull     mt <$> parseField r 6 numeric)  -- dictBaseType
      <<*> parseField r 7 numeric                                  -- dictSize
      <<*> parseField r 8 numeric                                  -- dictAlign
      <<*> parseField r 9 numeric                                  -- dictOffset
      <<*> parseField r 10 numeric                                 -- dictFlags
      <**> (mdForwardRefOrNull     mt <$> parseField r 11 numeric) -- dictElements
      <<*> parseField r 12 numeric                                 -- dictRuntimeLang
      <**> (mdForwardRefOrNull     mt <$> parseField r 13 numeric) -- dictVTableHolder
      <**> (mdForwardRefOrNull     mt <$> parseField r 14 numeric) -- dictTemplateParams
      <**> (mdStringOrNull     ctx mt <$> parseField r 15 numeric) -- dictIdentifier
    return $! updateMetadataTableA
      (addDebugInfo isDistinct <$> (DebugInfoCompositeType <$> dict)) pm

  19 -> label "METADATA_SUBROUTINE_TYPE" $ do
    ctx        <- getContext
    isDistinct <- parseField r 0 nonzero
    dist       <- (getCompose :: Compose Parse m w -> Parse (m w)) $ DISubroutineType
      <<$> parseField r 1 numeric                                 -- distFlags
      <**> (mdForwardRefOrNull     mt <$> parseField r 2 numeric) -- distTypeArray
    return $! updateMetadataTableA
      (addDebugInfo isDistinct <$> (DebugInfoSubroutineType <$> dist)) pm

  20 -> label "METADATA_COMPILE_UNIT" $ do
    let recordSize = length (recordFields r)

    when (recordSize < 14 || recordSize > 19)
      (fail "Invalid record")

    ctx        <- getContext
    isDistinct <- parseField r 0 nonzero
    dicu       <- (getCompose :: Compose Parse m w -> Parse (m w)) $ DICompileUnit
      <<$> parseField r 1 numeric                                  -- dicuLanguage
      <**> (mdForwardRefOrNull     mt <$> parseField r 2 numeric)  -- dicuFile
      <**> (mdStringOrNull ctx mt     <$> parseField r 3 numeric)  -- dicuProducer
      <<*> parseField r 4 nonzero                                  -- dicuIsOptimized
      <**> (mdStringOrNull ctx mt     <$> parseField r 5 numeric)  -- dicuFlags
      <<*> parseField r 6 numeric                                  -- dicuRuntimeVersion
      <**> (mdStringOrNull ctx mt     <$> parseField r 7 numeric)  -- dicuSplitDebugFilename
      <<*> parseField r 8 numeric                                  -- dicuEmissionKind
      <**> (mdForwardRefOrNull     mt <$> parseField r 9 numeric)  -- dicuEnums
      <**> (mdForwardRefOrNull     mt <$> parseField r 10 numeric) -- dicuRetainedTypes
      <**> (mdForwardRefOrNull     mt <$> parseField r 11 numeric) -- dicuSubprograms
      <**> (mdForwardRefOrNull     mt <$> parseField r 12 numeric) -- dicuGlobals
      <**> (mdForwardRefOrNull     mt <$> parseField r 13 numeric) -- dicuImports
      <**> if recordSize <= 15
          then pure Nothing
          else mdForwardRefOrNull  mt <$> parseField r 15 numeric -- dicuMacros
    dicuDWOId <-
      if recordSize <= 14
      then pure 0
      else parseField r 14 numeric
    dicuSplitDebugInlining <-
      if recordSize <= 16
      then pure True
      else parseField r 16 nonzero
    let dicu' = dicu <*> dicuDWOId <*> pure dicuSplitDebugInlining
    return $! updateMetadataTableA
      (addDebugInfo isDistinct <$> (DebugInfoCompileUnit <$> dicu')) pm


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

    ctx        <- getContext
    isDistinct <- parseField r 0 nonzero -- isDistinct
    disp       <- (getCompose :: Compose Parse m w -> Parse (m w)) $ DISubprogram
      <$$> (mdForwardRefOrNull     mt <$> parseField r 1 numeric)        -- dispScope
      <**> (mdStringOrNull ctx     mt <$> parseField r 2 numeric)        -- dispName
      <**> (mdStringOrNull ctx     mt <$> parseField r 3 numeric)        -- dispLinkageName
      <**> (mdForwardRefOrNull     mt <$> parseField r 4 numeric)        -- dispFile
      <<*> parseField r 5 numeric                                        -- dispLine
      <**> (mdForwardRefOrNull     mt <$> parseField r 6 numeric)        -- dispType
      <<*> parseField r 7 nonzero                                        -- dispIsLocal
      <<*> parseField r 8 nonzero                                        -- dispIsDefinition
      <<*> parseField r 9 numeric                                        -- dispScopeLine
      <**> (mdForwardRefOrNull     mt <$> parseField r 10 numeric)       -- dispContainingType
      <<*> parseField r 11 numeric                                       -- dispVirtuality
      <<*> parseField r 12 numeric                                       -- dispVirtualIndex
      <<*> (if hasThisAdjustment
          then parseField r 19 numeric
          else return 0)                                                 -- dispThisAdjustment
      <**> (if hasThrownTypes
          then mdForwardRefOrNull  mt <$> parseField r 20 numeric
          else return Nothing)                                           -- dispThrownTypes
      <<*> parseField r 13 numeric                                       -- dispFlags
      <<*> parseField r 14 nonzero                                       -- dispIsOptimized
      <**> (mdForwardRefOrNull     mt <$> parseField r (adj 15) numeric) -- dispTemplateParams
      <**> (mdForwardRefOrNull     mt <$> parseField r (adj 16) numeric) -- dispDeclaration
      <**> (mdForwardRefOrNull     mt <$> parseField r (adj 17) numeric) -- dispVariables
    -- TODO: in the LLVM parser, it then goes into the metadata table
    -- and updates function entries to point to subprograms. Is that
    -- neccessary for us?
    return $! updateMetadataTableA
      (addDebugInfo isDistinct <$> (DebugInfoSubprogram <$> disp)) pm

  22 -> label "METADATA_LEXICAL_BLOCK" $ do
    when (length (recordFields r) /= 5)
      (fail "Invalid record")
    cxt        <- getContext
    isDistinct <- parseField r 0 nonzero
    dilb       <- (getCompose :: Compose Parse m w -> Parse (m w)) $ DILexicalBlock
      <$$> (mdForwardRefOrNull mt <$> parseField r 1 numeric) -- dilbScope
      <**> (mdForwardRefOrNull mt <$> parseField r 2 numeric) -- dilbFile
      <<*> parseField r 3 numeric                             -- dilbLine
      <<*> parseField r 4 numeric                             -- dilbColumn
    return $! updateMetadataTableA
      (addDebugInfo isDistinct <$> (DebugInfoLexicalBlock <$> dilb)) pm

  23 -> label "METADATA_LEXICAL_BLOCK_FILE" $ do
    when (length (recordFields r) /= 4)
      (fail "Invalid record")

    cxt        <- getContext
    isDistinct <- parseField r 0 nonzero
    dilbf      <- (getCompose :: Compose Parse m w -> Parse (m w)) $ DILexicalBlockFile 
      <$$> (mdForwardRefOrNull mt <$> parseField r 1 numeric)
      <<*> (mdForwardRefOrNull mt <$> parseField r 2 numeric) -- dilbfFile
      <<*> parseField r 3 numeric                             -- dilbfDiscriminator

    let x :: _
        x = dilbf
    case (dilbf :: _) of
      Just dilbf' ->
        return $! updateMetadataTable
          (addDebugInfo isDistinct (DebugInfoLexicalBlockFile dilbf')) pm
      Nothing -> fail "Invalid record: scope field not present"

  24 -> label "METADATA_NAMESPACE" $ do
    isNew <- case length (recordFields r) of
               3 -> return True
               5 -> return False
               _ -> fail "Invalid METADATA_NAMESPACE record"
    let nameIdx = if isNew then 2 else 3
    cxt        <- getContext
    isDistinct <- parseField r 0 nonzero
    dins       <- (getCompose :: Compose Parse m w -> Parse (m w)) $ DINameSpace
      <$$> (mdString cxt mt    <$> parseField r nameIdx numeric) -- dinsName
      <**> (mdForwardRef mt    <$> parseField r 1 numeric)       -- dinsScope
      <**> (if isNew
            then return (ValMdString "")
            else mdForwardRef mt <$> parseField r 2 numeric)     -- dinsFile
      <<*> if isNew then return 0 else parseField r 4 numeric    -- dinsLine
    return $! updateMetadataTableA
      (addDebugInfo isDistinct <$> (DebugInfoNameSpace <$> dins)) pm

  25 -> label "METADATA_TEMPLATE_TYPE" $ do
    cxt        <- getContext
    isDistinct <- parseField r 0 nonzero
    dittp      <- (getCompose :: Compose Parse m w -> Parse (m w)) $ DITemplateTypeParameter
      <$$> (mdString cxt mt <$> parseField r 1 numeric) -- dittpName
      <**> (mdForwardRef mt <$> parseField r 2 numeric) -- dittpType
    return $! updateMetadataTableA
      (addDebugInfo isDistinct <$>
        (DebugInfoTemplateTypeParameter <$> dittp)) pm

  26 -> label "METADATA_TEMPLATE_VALUE" $ do
    cxt        <- getContext
    isDistinct <- parseField r 0 nonzero
    ditvp      <- (getCompose :: Compose Parse m w -> Parse (m w)) $ DITemplateValueParameter
      <$$> (mdString cxt mt <$> parseField r 1 numeric) -- ditvpName
      <**> (mdForwardRef mt <$> parseField r 2 numeric) -- ditvpType
      <**> (mdForwardRef mt <$> parseField r 3 numeric) -- ditvpValue
    return $! updateMetadataTableA
      (addDebugInfo isDistinct <$>
        (DebugInfoTemplateValueParameter <$> ditvp)) pm

  27 -> label "METADATA_GLOBAL_VAR" $ do
    let len = length (recordFields r)
    unless (11 <= len && len <= 12)
      (fail "Unexpected number of record fields")

    ctx        <- getContext
    field0     <- parseField r 0 numeric
    let isDistinct = testBit field0 0
        _version   = shiftR  field0 1 :: Int

    digv <- (getCompose :: Compose Parse m w -> Parse (m w)) $ DIGlobalVariable
      <$$> (mdForwardRefOrNull     mt <$> parseField r 1 numeric)  -- digvScope
      <**> (mdStringOrNull     ctx mt <$> parseField r 2 numeric)  -- digvName
      <**> (mdStringOrNull     ctx mt <$> parseField r 3 numeric)  -- digvLinkageName
      <**> (mdForwardRefOrNull     mt <$> parseField r 4 numeric)  -- digvFile
      <<*> parseField r 5 numeric                                  -- digvLine
      <**> (mdForwardRefOrNull     mt <$> parseField r 6 numeric)  -- digvType
      <<*> parseField r 7 nonzero                                  -- digvIsLocal
      <<*> parseField r 8 nonzero                                  -- digvIsDefinition
      <**> (mdForwardRefOrNull     mt <$> parseField r 9 numeric)  -- digvVariable
      <**> (mdForwardRefOrNull     mt <$> parseField r 10 numeric) -- digvDeclaration
      <<*> if len > 11
           then Just                  <$> parseField r 11 numeric  -- digvAlignment
           else pure Nothing
    return $! updateMetadataTableA
      (addDebugInfo isDistinct <$> (DebugInfoGlobalVariable <$> digv)) pm

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

    dilv <- (getCompose :: Compose Parse m w -> Parse (m w)) $ DILocalVariable
      <$$> (mdForwardRefOrNull mt
              <$> parseField r (adj 1) numeric) -- dilvScope
      <**> (mdStringOrNull     ("dilvName" :ctx) mt
              <$> parseField r (adj 2) numeric) -- dilvName
      <**> (mdForwardRefOrNull mt
              <$> parseField r (adj 3) numeric) -- dilvFile
      <<*> parseField r (adj 4) numeric         -- dilvLine
      <**> (mdForwardRefOrNull mt
              <$> parseField r (adj 5) numeric) -- dilvType
      <<*> parseField r (adj 6) numeric         -- dilvArg
      <<*> parseField r (adj 7) numeric         -- dilvFlags
    return $! updateMetadataTableA
      (addDebugInfo isDistinct <$> (DebugInfoLocalVariable <$> dilv)) pm

  29 -> label "METADATA_EXPRESSION" $ do
    let recordSize = length (recordFields r)
    when (recordSize < 1)
      (fail "Invalid record")
    isDistinct <- parseField r 0 nonzero
    diExpr     <- DebugInfoExpression . DIExpression <$> parseFields r 1 numeric
    return $! updateMetadataTable (addDebugInfo isDistinct diExpr) pm

  30 -> label "METADATA_OBJC_PROPERTY" $ fail "not yet implemented" -- TODO
  31 -> label "METADATA_IMPORTED_ENTITY" $ do
    cxt        <- getContext
    isDistinct <- parseField r 0 nonzero
    diie       <- (getCompose :: Compose Parse m w -> Parse (m w)) $ DIImportedEntity
      <<$> parseField r 1 numeric                             -- diieTag
      <**> (mdString       cxt mt <$> parseField r 5 numeric) -- diieName
      <**> (mdForwardRefOrNull mt <$> parseField r 2 numeric) -- diieScope
      <**> (mdForwardRefOrNull mt <$> parseField r 3 numeric) -- diieEntity
      <<*> parseField r 4 numeric                             -- diieLine

    return $! updateMetadataTableA
      (addDebugInfo isDistinct <$> (DebugInfoImportedEntity <$> diie)) pm

  32 -> label "METADATA_MODULE" $
    -- cxt <- getContext
    -- isDistinct <- parseField r 0 numeric
    -- mdForwardRefOrNull mt <$> parseField r 1 numeric
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
    -- mdForwardRefOrNull mt <$> parseField r 3 numeric
    -- mdForwardRefOrNull mt <$> parseField r 4 numeric
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
                          (str, rest) -> (rest, Char8.unpack str)
    return $! updateMetadataTable (addStrings strings) pm

  -- [ valueid, n x [id, mdnode] ]
  36 -> label "METADATA_GLOBAL_DECL_ATTACHMENT" $ do

    -- the record will always be of odd length
    when (mod (length (recordFields r)) 2 == 0)
         (fail "Invalid record")

    valueId <- parseField r 0 numeric
    sym     <- case lookupValueTableAbs valueId vt of
                 Just Typed{ typedValue = ValSymbol sym } -> pure sym
                 _ -> fail "Non-global referenced"

    refs <- parseGlobalObjectAttachment mt r

    return $! addGlobalAttachments sym refs pm

  37 -> label "METADATA_GLOBAL_VAR_EXPR" $ do
    when (length (recordFields r) /= 3)
      (fail "Invalid record: unsupported layout")
    cxt        <- getContext
    isDistinct <- parseField r 0 nonzero
    digve      <- (getCompose :: Compose Parse m w -> Parse (m w)) $ DIGlobalVariableExpression
      <$$> (mdForwardRefOrNull mt <$> parseField r 1 numeric) -- digveVariable
      <**> (mdForwardRefOrNull mt <$> parseField r 2 numeric) -- digveExpression
    return $! updateMetadataTableA
      (addDebugInfo isDistinct <$> (DebugInfoGlobalVariableExpression <$> digve)) pm

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
  -- TODO: is it OK to skip this if we always parse everything?
  39 -> label "METADATA_INDEX" $ pure pm

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
       go cxt (Map.insert kind (mdForwardRef mt i) acc) (n + 2)

  go _ acc _ = pure acc


-- | Parse a metadata node.
parseMetadataNode :: Functor f
                  => Bool
                  -> MetadataTable
                  -> Record
                  -> PartialMetadata f
                  -> Parse (PartialMetadata f)
parseMetadataNode isDistinct mt r pm = do
  ixs <- parseFields r 0 numeric
  cxt <- getContext
  let foo = traverse (commuteMaybe . mdForwardRefOrNull mt) ixs
  return $! updateMetadataTableA
    (addNode isDistinct <$> foo) pm


-- | Parse out a metadata node in the old format.
parseMetadataOldNode :: Functor m
                     => Bool
                     -> ValueTable
                     -> MetadataTable
                     -> Record
                     -> PartialMetadata m
                     -> Parse (PartialMetadata m)
parseMetadataOldNode fnLocal vt mt r pm = do
  values <- loop =<< parseFields r 0 numeric
  return $! updateMetadataTable (addOldNode fnLocal values) pm
  where
  loop :: _ -> Parse (m (Typed PValue))
  loop fs = case fs of

    tyId:valId:rest -> do
      cxt <- getContext
      ty  <- getType' tyId
      val <- case ty of
        PrimType Metadata -> return $ Typed (PrimType Metadata)
                                            (ValMd (mdForwardRef mt valId))
        -- XXX need to check for a void type here
        _                 -> return (forwardRef cxt valId vt)

      vals <- loop rest
      return (val:vals)

    [] -> return []

    _ -> fail "Malformed metadata node"

parseMetadataKindEntry :: Record -> Parse ()
parseMetadataKindEntry r = do
  kind <- parseField  r 0 numeric
  name <- parseFields r 1 char
  addKind kind (UTF8.decode name)
