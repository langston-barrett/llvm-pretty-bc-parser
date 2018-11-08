{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE RecordWildCards #-}
{-|
Module      : Data.LLVM.BitCode.Debug
Description : Utilities for debugging the parser
Copyright   : (c) Galois, Inc 2018
License     : BSD-3
Maintainer  : atomb@galois.com
Stability   : experimental
-}

module Data.LLVM.BitCode.Debug where

import Data.LLVM.BitCode.Bitstream
import Data.LLVM.BitCode.Record

import qualified Text.PrettyPrint.Leijen as PP
import           Text.PrettyPrint.Leijen ((<$$>), (<+>), text)
import qualified Text.LLVM.PP as LLVMPP

import           Data.LLVM.BitCode.Parse
import qualified Data.Map.Strict as Map
import           Data.Map.Strict (Map)
import           Data.Maybe (maybe, mapMaybe)

-- formatError :: Error -> String
-- formatError = show . ppError

-- ppError :: Error -> PP.Doc
-- ppError Error{..}
--   | null errContext = text $ errMessage
--   | otherwise       = text
--                     $ unlines
--                     $ errMessage
--                     : "from:"
--                     : map ('\t' :) errContext
--                     ++ "state:" : [show (ppParseState errState)]

nestAlignVsep :: PP.Doc -> [PP.Doc] -> PP.Doc
nestAlignVsep d [] = d
nestAlignVsep d ds =
  PP.nest 2 (d <$$> PP.align (PP.vsep ds))

ts :: forall a. Show a => a -> PP.Doc
ts = text . show

ppMap :: (a -> PP.Doc) -> (b -> PP.Doc) -> Map a b -> PP.Doc
ppMap ppa ppb m = PP.encloseSep PP.lbrace PP.rbrace PP.comma $
  map (\(k, v) -> ppa k <+> text ":=" <+> ppb v) $ Map.toList m

-- | Print a generic datatype with named fields.
ppRecord :: String             -- ^ Name of the datatype
         -> [(String, PP.Doc)] -- ^ Fields
         -> PP.Doc
ppRecord name fields =
  PP.nest 2 (text (name ++ ":")
             <$$> PP.align (PP.vsep (map (\(x, y) -> text (x ++ ":") <+> y)
                                         fields)))

-- | Print the nested block IDs
--
-- Useful for debugging.
ppBlocks :: [Entry] -> PP.Doc
ppBlocks entries = PP.vsep (mapMaybe ppBlock entries)
  where ppBlock :: Entry -> Maybe PP.Doc
        ppBlock (EntryBlock Block{..}) = Just $
          nestAlignVsep (ts blockId) (mapMaybe ppBlock blockEntries)
        ppBlock _ = Nothing

-- ppValueTable :: ValueTable -> PP.Doc
-- ppValueTable ValueTable{..} =
--   ppRecord "Value table" $
--     [ ("Next ID ",       ts valueNextId)
--     , ("strtab ",        ppMap ts ts strtabEntries)
--     , ("Entries ",       text "TODO")
--          -- ppMap ts (LLVMPP.ppTyped (LLVMPP.ppValue' LLVMPP.integral)) valueEntries)
--     , ("Value rel IDs ", ts valueRelIds)
--     ]

-- ppParseState :: ParseState -> PP.Doc
-- ppParseState ParseState{..} =
--   ppRecord "Parse state" $
--     [ ("Type table",          ppMap ts (ts . LLVMPP.ppType) psTypeTable)
--     , ("Type table size",     ts psTypeTableSize)
--     , ("Value table",         ppValueTable psValueTable)
--     , ("String table",        text "TODO")
--     , ("Metadata table",      text "TODO")
--     , ("Metadata refs",       text "TODO")
--     , ("Function prototypes", text "TODO")
--     , ("Next result ID",      ts psNextResultId)
--     , ("Type name",           maybeStr psTypeName)
--     , ("Next type ID",        ts psNextTypeId)
--     , ("Last location",       text "TODO")
--     , ("Kind table",          text "TODO")
--     , ("Mod version",         text "TODO")
--     ]
--   where maybeStr = maybe (ts "[none]") ts
