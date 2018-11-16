{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-|
Module      : Data.LLVM.BitCode.IR.Metadata
Description : Parsing metadata blocks
Copyright   : (c) Galois, Inc 2018
License     : BSD-3
Maintainer  : atomb@galois.com
Stability   : experimental
-}

module Data.LLVM.BitCode.IR.Metadata (
    preparseMetadata
  , parseMetadataKindEntry
  , PartialUnnamedMd(..)
  , finalizePartialUnnamedMd
  , finalizePValMd
  , addMetadataType
  , InstrMdAttachments
  , PFnMdAttachments
  , PKindMd
  , PGlobalAttachments
  , ParsedMetadata
  ) where

import qualified MonadLib as ML
import qualified MonadLib.Monads as ML
import           Lens.Micro
import           Control.Arrow ((>>>))
import           Control.Monad (foldM)
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.Maybe (mapMaybe)
import           Data.Text (unpack)
import           Data.Validation

import           Text.LLVM.AST

import           Data.LLVM.BitCode.Bitstream (Entry)
import           Data.LLVM.BitCode.Parse

import           Data.LLVM.BitCode.Match ((|||))
import qualified Data.LLVM.BitCode.IR.Blocks as Blk

import           Data.LLVM.BitCode.IR.Metadata.Applicative
import           Data.LLVM.BitCode.IR.Metadata.Counter
import           Data.LLVM.BitCode.IR.Metadata.Finalize
import           Data.LLVM.BitCode.IR.Metadata.Parse
import           Data.LLVM.BitCode.IR.Metadata.Resolve
import           Data.LLVM.BitCode.IR.Metadata.Table

import Debug.Trace

type ParsedMetadata =
  ( [NamedMd]
  , ([PartialUnnamedMd], [PartialUnnamedMd])
  , InstrMdAttachments
  , PFnMdAttachments
  , PGlobalAttachments
  )

-- | Find and parse metadata blocks, resolving cross-references among them.
preparseMetadata :: ValueTable
                 -> [Entry]
                 -> Parse ParsedMetadata
preparseMetadata valTab entries =
  -- First, we filter into any entries that contain metadata blocks.
  let fnMatch = Blk.functionBlockId
              >>> fmap (mapMaybe (Blk.metadataBlockId ||| Blk.metadataAttachmentBlockId))
              >>> fmap concat
      mdEntries =
        concat $! mapMaybe Blk.metadataBlockId entries ++
                 mapMaybe fnMatch entries
  in label "METADATA_BLOCK" $! do

    -- Prepare the initial metadata table
    mdt <- getMdTable
    let mdt' = mdt { valueEntries = Map.map pure $! valueEntries mdt }
    let pm0  = emptyPartialMetadata 0 mdt'

    -- The accumulator for this fold is the intermediate state of metadata
    -- parsing, consisting of
    -- 1. The number of unnamed metadata seen so far (implicit IDs)
    -- 2. The 'PartialMetadata' structure
    pm <- foldM (\pm -> parseMetadataEntry valTab (pm ^. pmEntries) pm) pm0 mdEntries

    -- Now, we resolve references among metadata.

    -- In the 'Writer Text/State (Map k v)' monad
    let ((t, log), (_, st)) =
          ML.runState (zeroCtr, Map.empty) . ML.runWriterT $! do

            -- Resolve references in the 'MetadataTable'
            vte' <- resolveAll $ valueEntries $! pm ^. pmEntries . mtEntries

            -- Resolve other references in the partial metadata
            -- With certain of these, the applicative effect is nested pretty
            -- deeply, so we need to bring it up a few levels
            -- (e.g. 'pmInstrAttachments').
            namedGlobals'   <- trace "namedGlobals" $! resolveAllList $! namedEntries pm
            unnamedGlobals' <- trace "unnamedGlobals" $! resolveOne $!
              (\(a, b) -> tupleA2 (sequenceA a, sequenceA b)) (unnamedEntries pm)
            instrAtt'       <- trace "instrAtt" $! resolveAllMap $!
              traverse (\(a, b) -> tupleA2 (pure a, b)) <$>
                (pm ^. pmInstrAttachments)
            fnAtt'          <- trace "fnAtt"   $! resolveAllMap (pm ^. pmFnAttachments)
            globAtt'        <- trace "globAtt" $! resolveAllMap $! seqMap <$> pm ^. pmGlobalAttachments
            -- globAtt'        <- (undefined :: _ (Validation Int _))

            pure (vte', namedGlobals', unnamedGlobals', instrAtt', fnAtt', globAtt')

    case t of
      ( Success !vte, Success !namedGlobals, Success !unnamedGlobals
        , Success !fnAtt, Success !instrAtt, Success !globAtt) ->
        do -- Update the parser's state with the new metadata table
           let vte' = (pm ^. pmEntries . mtEntries) { valueEntries  = vte }
           setMdTable vte'
           setMdRefs  $! mkMdRefTable $! (pm ^. pmEntries) { _mtEntries = vte' }
           pure (namedGlobals, unnamedGlobals, fnAtt, instrAtt, globAtt)

      (vte, namedGlobals, unnamedGlobals, fnAtt, instrAtt, globAtt) ->
        fail $! unlines $!
            [ "Metadata block contained some unresolvable entries."
            , "This is usually a result of an internal error."
            , "Here are the (referencer, referencee) pairs"
            , "(list may be incomplete):"
            , concat . concat $!
                let mkErr :: Show a => Validation a c -> [String]
                    mkErr = validation ((:[]) . (++"\n") . show) (const [])
                in [ mkErr vte
                   , mkErr namedGlobals
                   , mkErr unnamedGlobals
                   , mkErr instrAtt
                   , mkErr fnAtt
                   , mkErr globAtt
                   ]
            , "Here is the set of keys present in the state: "
            , show $ Map.keysSet st
            , "Here is the set of unnamed metadata keys: "
            , show $ Map.keysSet <$> vte
            , "Here is (maybe) the difference between the state and desired state: "
            , show $ Set.difference <$> (Map.keysSet <$> vte) <*> pure (Map.keysSet st)
            , "And here is a log: "
            , "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ LOG"
            ] ++ map unpack log
