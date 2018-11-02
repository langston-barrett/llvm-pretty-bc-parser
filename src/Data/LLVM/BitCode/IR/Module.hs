{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Data.LLVM.BitCode.IR.Module where

import           Data.LLVM.BitCode.Bitstream
import           Data.LLVM.BitCode.IR.Attrs
import           Data.LLVM.BitCode.IR.Blocks
import           Data.LLVM.BitCode.IR.Constants
import           Data.LLVM.BitCode.IR.Function
import           Data.LLVM.BitCode.IR.Globals
import           Data.LLVM.BitCode.IR.Metadata
import           Data.LLVM.BitCode.IR.Metadata.Resolve
import           Data.LLVM.BitCode.IR.Types
import           Data.LLVM.BitCode.IR.Values
import           Data.LLVM.BitCode.Match
import           Data.LLVM.BitCode.Parse
import           Data.LLVM.BitCode.Record
import           Text.LLVM.AST

import qualified Codec.Binary.UTF8.String as UTF8 (decode)
import           Control.Lens hiding (ix)
import           Control.Monad (foldM,guard,when,forM_)
import           Control.Monad.Fail (MonadFail)
import           Data.Bifunctor
import qualified Data.Foldable as F
import           Data.Functor.Compose
import           Data.List (sortBy)
import qualified Data.Map as Map
import           Data.Ord (comparing)
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Text as Text
import qualified Data.Traversable as T
import           Data.Validation (Validation(..), validation)
import           MonadLib (Id, runId)
import           MonadLib.Monads (runState, runWriterT)


-- Module Block Parsing --------------------------------------------------------

data PartialModule f = PartialModule
  { partialGlobalIx   :: !Int
  , partialGlobals    :: GlobalListF f
  , partialDefines    :: DefineListF f
  , partialDeclares   :: DeclareList
  , partialDataLayout :: DataLayout
  , partialInlineAsm  :: InlineAsm
  , partialComdat     :: Seq (String,SelectionKind)
  , partialAliasIx    :: !Int
  , partialAliases    :: AliasList
  , partialNamedMd    :: [f NamedMd]
  , partialUnnamedMd  :: [PartialUnnamedMdF f]
  , partialSections   :: Seq String
  , partialSourceName :: !(Maybe String)
  }

emptyPartialModule :: PartialModule f
emptyPartialModule  = PartialModule
  { partialGlobalIx   = 0
  , partialGlobals    = mempty
  , partialDefines    = mempty
  , partialDeclares   = mempty
  , partialDataLayout = mempty
  , partialInlineAsm  = mempty
  , partialAliasIx    = 0
  , partialAliases    = mempty
  , partialNamedMd    = mempty
  , partialUnnamedMd  = mempty
  , partialSections   = mempty
  , partialSourceName = mempty
  , partialComdat     = mempty
  }


-- | Fixup the global variables and declarations and resolve forward
-- references in metadata, and return the completed module.
finalizeModule :: PartialModule (LookupMd (SEW Int PValMd))
               -> Parse Module
finalizeModule pm = label "finalizeModule" $ do
  (namedMd, unnamedMd, globs, defs) <-
    finalizeMdRefs
      (partialUnnamedMd pm)
      (partialNamedMd pm)
      (partialGlobals pm)
      (partialDefines pm)
  globals  <- T.mapM finalizeGlobal       globs
  declares <- T.mapM finalizeDeclare      (partialDeclares pm)
  aliases  <- T.mapM finalizePartialAlias (partialAliases pm)
  unnamed  <- T.mapM finalizePartialUnnamedMd (unnamedMd)
  types    <- resolveTypeDecls
  let lkp = lookupBlockName defs
  defines  <- T.mapM (finalizePartialDefine lkp) defs
  return emptyModule
    { modDataLayout = partialDataLayout pm
    , modNamedMd    = namedMd
    , modUnnamedMd  = sortBy (comparing umIndex) unnamed
    , modGlobals    = F.toList globals
    , modDefines    = F.toList defines
    , modTypes      = types
    , modDeclares   = F.toList declares
    , modInlineAsm  = partialInlineAsm pm
    , modAliases    = F.toList aliases
    , modComdat     = Map.fromList (F.toList (partialComdat pm))
    }

-- | Finalize metadata, resolving references.
--
-- If there are unresolvable refs, this will fail with a comprehensive
-- message.
--
-- This is in this module and not "Data.LLVM.BitCode.IR.Metadata.Resolve"
-- because awareness of e.g. 'GlobalList' and 'DefineList' crosses module
-- boundaries.
finalizeMdRefs :: (MonadFail m)
               => [PartialUnnamedMdF (LookupMd (SEW Int PValMd))]
               -> [LookupMd (SEW Int PValMd) NamedMd]
               -> GlobalListF (LookupMd (SEW Int PValMd))
               -> DefineListF (LookupMd (SEW Int PValMd))
               -> m ( [NamedMd]
                    , [PartialUnnamedMd]
                    , GlobalList
                    , DefineList PValMd
                    )
finalizeMdRefs unnamed named globList defList = do
  -- In the 'Writer Text/State (Map k v)' monad
  let ((unnamed', named', globList', defList'), log) =
        fst . runState Map.empty . runWriterT $ do
          -- Turn the 'PartialUnnamedMd' back into a 'Map'
          let pumTable :: Map.Map Int (LookupMd (SEW Int PValMd) PValMd)
              pumTable = Map.fromList $ map (\pum -> (pum ^. pumIndex, pum ^. pumValues )) unnamed

          -- Resolve references, updating the state
          _          <- resolveAll pumTable

          -- The references are buried a little deep here.
          -- Lenses are a resonable, yet still complex way to do it.
          let traverseCompose :: (Applicative m, Semigroup w)
                              => Traversal s s' b b'
                              -> (b -> m (Validation w b'))
                              -> s
                              -> m (Validation w s')
              traverseCompose l f s = getCompose (l (Compose . f) s)

          -- Replace the semigroup constraint by list-making
          let traverseCompose' :: (Applicative m)
                               => Traversal s s' b b'
                               -> (b -> m (Validation w b'))
                               -> s
                               -> m (Validation [w] s')
              traverseCompose' l f s = traverseCompose l (fmap (first (:[])) . f) s

          -- Resolve references with the current state
          unnamed''  <- traverseCompose' (traverse . pumValues) resolveOne unnamed
          named''    <- resolveAllList named

          globList'' <- traverseCompose (traverse . pgMd) resolveAllMap globList
          defList''  <-
            -- tr resolves some metadata reference deep down in the DefineList
            let tr :: Traversal (DefineListF (LookupMd f)) (DefineListF Id)
                                (LookupMd f PValMd) (Id PValMd)
                tr = traverse . partialGlobalMd . traverse -- . pumValues
            in traverseCompose' tr (fmap (fmap pure) . resolveOne) defList

          pure (unnamed'', named'', globList'', defList'')

  case (unnamed', named', globList', defList') of
    (Success unnamed'', Success named'', Success globList'', Success defList'') ->
      let fixDL :: DefineListF Id -> DefineList PValMd
          fixDL dl = runId $ (each . partialGlobalMd . each) id dl
      in pure (named'', unnamed'', globList'', fixDL defList'')
    _ -> fail $ unlines $
            [ "Metadata block contained some unresolvable entries."
            , "This is usually a result of an internal error."
            , "Here are the (referencer, referencee) pairs"
            , "(list may be incomplete):"
            , concat . concat $
                let mkErr :: Show a => Validation a c -> [String]
                    mkErr = validation ((:[]) . (++"\n") . show) (const [])
                in [ mkErr unnamed'
                   , mkErr named'
                   , mkErr globList'
                   , mkErr defList'
                   ]
            , "\nAnd here is a log: "
            ] ++ map Text.unpack log

-- | Parse an LLVM Module out of the top-level block in a Bitstream.
parseModuleBlock :: [Entry] -> Parse Module
parseModuleBlock ents = label "MODULE_BLOCK" $ do

  -- the explicit type symbol table has been removed in 3.1, so we parse the
  -- type table, and generate the type symbol table from it.
  tsymtab <- label "type symbol table" $ do
    mb <- match (findMatch typeBlockIdNew) ents
    case mb of
      Just es -> parseTypeBlock es
      Nothing -> return mempty

  withTypeSymtab tsymtab $ label "value symbol table" $ do
    -- parse the value symbol table out first, if there is one
    symtab <- do
      mb <- match (findMatch valueSymtabBlockId) ents
      case mb of
        Just es -> parseValueSymbolTableBlock es
        Nothing -> return emptyValueSymtab

    pm <- withValueSymtab symtab
        $ foldM parseModuleBlockEntry emptyPartialModule ents

    finalizeModule pm


-- | Parse the entries in a module block.
parseModuleBlockEntry :: Applicative f
                      => PartialModule (LookupMd f)
                      -> Entry
                      -> Parse (PartialModule (LookupMd f))

parseModuleBlockEntry pm (blockInfoBlockId -> Just _) =
  -- skip the block info block, as we only use it during Bitstream parsing.
  return pm

parseModuleBlockEntry pm (typeBlockIdNew -> Just _) = do
  -- TYPE_BLOCK_ID_NEW
  -- this is skipped, as it's parsed before anything else, in parseModuleBlock
  return pm

parseModuleBlockEntry pm (constantsBlockId -> Just es) = do
  -- CONSTANTS_BLOCK_ID
  parseConstantsBlock es
  return pm

parseModuleBlockEntry pm (moduleCodeFunction -> Just r) = do
  -- MODULE_CODE_FUNCTION
  parseFunProto r pm

parseModuleBlockEntry pm (functionBlockId -> Just es) = label "FUNCTION_BLOCK_ID" $ do
  let unnamedGlobalsCount = length (partialUnnamedMd pm)
  def <- parseFunctionBlock unnamedGlobalsCount es
  let def' = def { _partialGlobalMd = [] }
  return pm { partialDefines   = partialDefines pm Seq.|> def'
            , partialUnnamedMd = _partialGlobalMd def ++ partialUnnamedMd pm
            }

parseModuleBlockEntry pm (paramattrBlockId -> Just _) = do
  -- PARAMATTR_BLOCK_ID
  -- TODO: skip for now
  return pm

parseModuleBlockEntry pm (paramattrGroupBlockId -> Just _) = do
  -- PARAMATTR_GROUP_BLOCK_ID
  -- TODO: skip for now
  return pm

parseModuleBlockEntry pm (metadataBlockId -> Just es) = label "METADATA_BLOCK_ID" $ do
  vt <- getValueTable
  let globalsSoFar = length (partialUnnamedMd pm)
  (ns, (gs, _), _, _, atts) <- parseMetadataBlock globalsSoFar vt es
  return $ addGlobalAttachments atts pm
    { partialNamedMd   = partialNamedMd   pm ++ ns
    , partialUnnamedMd = partialUnnamedMd pm ++ gs
    }

parseModuleBlockEntry pm (valueSymtabBlockId -> Just _es) = do
  -- VALUE_SYMTAB_BLOCK_ID
  -- NOTE: we parse the value symbol table eagerly at the beginning of the
  -- MODULE_BLOCK
  return pm

parseModuleBlockEntry pm (moduleCodeTriple -> Just _) = do
  -- MODULE_CODE_TRIPLE
  return pm

parseModuleBlockEntry pm (moduleCodeDatalayout -> Just r) = do
  -- MODULE_CODE_DATALAYOUT
  layout <- UTF8.decode <$> parseFields r 0 char
  case parseDataLayout layout of
    Nothing -> fail ("unable to parse data layout: ``" ++ layout ++ "''")
    Just dl -> return (pm { partialDataLayout = dl })

parseModuleBlockEntry pm (moduleCodeAsm -> Just r) = do
  -- MODULE_CODE_ASM
  asm <- UTF8.decode <$> parseFields r 0 char
  return pm { partialInlineAsm = lines asm }

parseModuleBlockEntry pm (abbrevDef -> Just _) = do
  -- skip abbreviation definitions
  return pm

parseModuleBlockEntry pm (moduleCodeGlobalvar -> Just r) = do
  -- MODULE_CODE_GLOBALVAR
  pg <- parseGlobalVar (partialGlobalIx pm) r
  return pm
    { partialGlobalIx = succ (partialGlobalIx pm)
    , partialGlobals  = partialGlobals pm Seq.|> pg
    }

parseModuleBlockEntry pm (moduleCodeAlias -> Just r) = label "MODULE_CODE_ALIAS_OLD" $ do
  pa <- parseAliasOld (partialAliasIx pm) r
  return pm
    { partialAliasIx = succ (partialAliasIx pm)
    , partialAliases = partialAliases pm Seq.|> pa
    }

parseModuleBlockEntry pm (moduleCodeVersion -> Just r) = do
  -- MODULE_CODE_VERSION

  -- please see:
  -- http://llvm.org/docs/BitCodeFormat.html#module-code-version-record
  version <- parseField r 0 numeric
  setModVersion version
  case version :: Int of
    0 -> setRelIds False  -- Absolute value ids in LLVM <= 3.2
    1 -> setRelIds True   -- Relative value ids in LLVM >= 3.3
    2 -> setRelIds True   -- Relative value ids in LLVM >= 5.0
    _ -> fail ("unsupported version id: " ++ show version)

  return pm

parseModuleBlockEntry pm (moduleCodeSectionname -> Just r) = do
  name <- UTF8.decode <$> parseFields r 0 char
  return pm { partialSections = partialSections pm Seq.|> name }

parseModuleBlockEntry pm (moduleCodeComdat -> Just r) = do
  -- MODULE_CODE_COMDAT
  when (length (recordFields r) < 2) (fail "Invalid record (MODULE_CODE_COMDAT)")
  v <- getModVersion
  (kindVal, name) <- if | v >= 2 -> do
                            kindVal <- parseField r 0 numeric
                            name    <- UTF8.decode <$> parseFields r 2 char
                            return (kindVal, name)
                        | otherwise -> do
                            offset  <- parseField r 0 numeric
                            len     <- parseField r 1 numeric
                            kindVal <- parseField r 2 numeric
                            mst     <- getStringTable
                            let msg = "No string table for new-style COMDAT."
                            st      <- maybe (fail msg) return mst
                            let Symbol name = resolveStrtabSymbol st offset len
                            return (kindVal, name)
  kind <- case kindVal :: Int of
            1  -> pure ComdatAny
            2  -> pure ComdatExactMatch
            3  -> pure ComdatLargest
            4  -> pure ComdatNoDuplicates
            5  -> pure ComdatSameSize
            _  -> pure ComdatAny -- This matches the C++ code as of 7d085b607d
  return pm { partialComdat = partialComdat pm Seq.|> (name,kind) }

parseModuleBlockEntry pm (moduleCodeVSTOffset -> Just _) = do
  -- MODULE_CODE_VSTOFFSET
  -- TODO: should we handle this?
  return pm

parseModuleBlockEntry pm (moduleCodeAliasNew -> Just r) = label "MODULE_CODE_ALIAS" $ do
  pa <- parseAlias r
  return pm
    { partialAliasIx = succ (partialAliasIx pm)
    , partialAliases = partialAliases pm Seq.|> pa
    }

parseModuleBlockEntry pm (moduleCodeMDValsUnused -> Just _) = do
  -- MODULE_CODE_METADATA_VALUES_UNUSED
  return pm

parseModuleBlockEntry pm (moduleCodeSourceFilename -> Just r) = do
  -- MODULE_CODE_SOURCE_FILENAME
  do str <- parseField r 0 cstring
     return pm { partialSourceName = Just str }

parseModuleBlockEntry pm (moduleCodeHash -> Just _) = do
  -- MODULE_CODE_HASH
  -- It should be safe to ignore this for now.
  --fail "MODULE_CODE_HASH"
  return pm

parseModuleBlockEntry _ (moduleCodeIFunc -> Just _) = do
  -- MODULE_CODE_IFUNC
  fail "MODULE_CODE_IFUNC"

parseModuleBlockEntry pm (uselistBlockId -> Just _) = do
  -- USELIST_BLOCK_ID
  -- XXX ?? fail "USELIST_BLOCK_ID"
  return pm

parseModuleBlockEntry _ (moduleStrtabBlockId -> Just _) = do
  -- MODULE_STRTAB_BLOCK_ID
  fail "MODULE_STRTAB_BLOCK_ID"

parseModuleBlockEntry pm (globalvalSummaryBlockId -> Just _) = do
  -- GLOBALVAL_SUMMARY_BLOCK_ID
  -- It should be safe to ignore this for now.
  return pm

parseModuleBlockEntry pm (operandBundleTagsBlockId -> Just _) = do
  -- OPERAND_BUNDLE_TAGS_BLOCK_ID
  -- fail "OPERAND_BUNDLE_TAGS_BLOCK_ID"
  return pm

parseModuleBlockEntry pm (metadataKindBlockId -> Just es) = label "METADATA_KIND_BLOCK_ID" $ do
  forM_ es $ \e ->
    case fromEntry e of
      Just r -> parseMetadataKindEntry r
      Nothing -> fail "Can't parse metadata kind block entry."
  return pm

parseModuleBlockEntry pm (strtabBlockId -> Just _) =
  -- Handled already.
  return pm

parseModuleBlockEntry pm (ltoSummaryBlockId -> Just _) =
  -- It should be safe to ignore this for now.
  --label "FULL_LTO_GLOBALVAL_SUMMARY_BLOCK_ID" $ do
  --  fail "FULL_LTO_GLOBALVAL_SUMMARY_BLOCK_ID unsupported"
  return pm

parseModuleBlockEntry pm (symtabBlockId -> Just [symtabBlobId -> Just _]) =
  -- Handled already
  return pm

parseModuleBlockEntry pm (syncScopeNamesBlockId -> Just _) =
  label "SYNC_SCOPE_NAMES_BLOCK_ID" $ do
    -- TODO: record this information somewhere
    return pm

parseModuleBlockEntry _ e =
  fail ("unexpected module block entry: " ++ show e)

parseFunProto :: Record -> PartialModule f -> Parse (PartialModule f)
parseFunProto r pm = label "FUNCTION" $ do
  ix   <- nextValueId
  (name, offset) <- oldOrStrtabName ix r
  let field i = parseField r (i + offset)
  funTy   <- getType =<< field 0 numeric
  let ty = case funTy of
             PtrTo _  -> funTy
             _        -> PtrTo funTy

  isProto <-             field 2 numeric

  link    <-             field 3 linkage

  section <-
    if length (recordFields r) >= 6
       then do sid <- field 6 numeric
               if sid == 0
                  then return Nothing
                  else do let sid' = sid - 1
                          when (sid' >= Seq.length (partialSections pm))
                              (fail "invalid section name index")
                          return (Just (Seq.index (partialSections pm) sid'))

       else return Nothing

  -- push the function type
  _    <- pushValue (Typed ty (ValSymbol name))
  let lkMb t x
       | Seq.length t > x = Just (Seq.index t x)
       | otherwise        = Nothing
  comdat <- if length (recordFields r) >= 12
               then do comdatID <- field 12 numeric
                       pure (fst <$> partialComdat pm `lkMb` comdatID)
               else pure Nothing
  let proto = FunProto
        { protoType  = ty
        , protoLinkage =
          do -- we emit a Nothing here to maintain output compatibility with
             -- llvm-dis when linkage is External
             guard (link /= External)
             return link
        , protoGC     = Nothing
        , protoSym    = name
        , protoIndex  = ix
        , protoSect   = section
        , protoComdat = comdat
        }

  if isProto == (0 :: Int)
     then pushFunProto proto >> return pm
     else return pm { partialDeclares = partialDeclares pm Seq.|> proto }

addGlobalAttachments :: PGlobalAttachmentsF f -> PartialModule f -> PartialModule f
addGlobalAttachments gs0 pm | Map.null gs0 = pm
addGlobalAttachments gs0 pm = pm { partialGlobals = go (partialGlobals pm) gs0 }
  where go gs atts =
          case Seq.viewl gs of
            Seq.EmptyL -> Seq.empty

            -- Try to find the current global in the given attachments
            -- If it's present, delete it.
            g Seq.:< gs' ->
              let (mb, atts') =
                    Map.updateLookupWithKey (\_ _ -> Nothing) (pgSym g) atts
              in case mb of
                    Just md -> g { _pgMd = md } Seq.<| go gs' atts'
                    Nothing -> g                Seq.<| go gs' atts'
