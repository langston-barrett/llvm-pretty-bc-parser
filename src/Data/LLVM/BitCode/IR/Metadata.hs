{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
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
    parseMetadataBlock
  , parseMetadataKindEntry
  , PartialUnnamedMd(..)
  , finalizePartialUnnamedMd
  , finalizePValMd
  , InstrMdAttachments
  , PFnMdAttachments
  , PKindMd
  , PGlobalAttachments
  , ParsedMetadata
  ) where

import           Lens.Micro
import           Control.Monad (foldM)
import qualified Data.Map  as Map

import           Text.LLVM.AST

import           Data.LLVM.BitCode.Bitstream (Entry)
import           Data.LLVM.BitCode.Parse

import           Data.LLVM.BitCode.IR.Metadata.Finalize
import           Data.LLVM.BitCode.IR.Metadata.Parse
import           Data.LLVM.BitCode.IR.Metadata.Table

type ParsedMetadata f =
  ( [f NamedMd]
  , ([f PartialUnnamedMd], [f PartialUnnamedMd])
  , InstrMdAttachments
  , PFnMdAttachments
  , PGlobalAttachments' f
  )

-- | This is the entrypoint parsing a metadata block, it is called from e.g.
-- 'parseModule'.
parseMetadataBlock :: forall f. Applicative f
                   => Int {- ^ globals seen so far -}
                   -> ValueTable
                   -> [Entry]
                   -> Parse (ParsedMetadata (LookupMd f))
parseMetadataBlock globals vt entries = label "METADATA_BLOCK" $ do

  -- Prepare the initial metadata table
  mdt <- getMdTable
  let mdt' = mdt { valueEntries = Map.map pure $ valueEntries mdt }
  let pm0  = emptyPartialMetadata globals mdt'

  -- Fold across all the entries
  pm <- foldM (\pm -> parseMetadataEntry vt (pm ^. pmEntries) pm) pm0 entries

  pure ( namedEntries pm
       , unnamedEntries pm
       , pm ^. pmInstrAttachments
       , pm ^. pmFnAttachments
       , pm ^. pmGlobalAttachments
       )

{-
  -- In the 'Writer Text/State (Map k v)' monad
  let ((vte', pga', pne'), log) =
        fst . runState Map.empty . runWriterT $ do

          -- Resolve references in the 'MetadataTable'
          vte' <- resolveAll' (valueEntries $ pm ^. pmEntries . mtEntries)

          -- Resolve other references in the partial metadata
          pga' <- resolveAll  (pm ^. pmGlobalAttachments)
          pne' <- resolveAll  (pm ^. pmNamedEntries)

          pure (vte', pga', pne')

_ -> fail $ unlines $
        [ "Metadata block contained some unresolvable entries."
        , "This is usually a result of an internal error."
        , "Here are the (referencer, referencee) pairs"
        , "(list may be incomplete):"
        , concat . concat $
            let foo :: Show a => Either a b -> [String]
                foo = either ((:[]) . show) (const [])
            in [ foo vte'
              , foo pga'
              , foo pne'
              ]
        , "\nAnd here is a log: "
        ] ++ map unpack log

  let vt = pm ^. pmEntries . mtEntries
      vt' :: ValueTable' (LookupMd f PValMd)
      vt' = ValueTable { valueNextId   = valueNextId vt
                       , valueEntries  = (valueEntries $ pm ^. pmEntries . mtEntries)
                       , strtabEntries = strtabEntries vt
                       , valueRelIds   = valueRelIds vt
                       }

      mt' :: MetadataTable' (LookupMd f)
      mt' = MetadataTable { _mtEntries  = vt'
                          , _mtNodes    = pm ^. pmEntries . mtNodes
                          , _mtNextNode = pm ^. pmEntries . mtNextNode
                          }

      -- Map.map (Typed (PrimType Metadata) . ValMd)
      pm' :: PartialMetadata (LookupMd f)
      pm' = PartialMetadata { _pmEntries           = mt'
                            , _pmNamedEntries      = pm ^. pmNamedEntries
                            , _pmGlobalAttachments = pm ^. pmGlobalAttachments
                            , _pmNextName          = pm ^. pmNextName
                            , _pmInstrAttachments  = pm ^. pmInstrAttachments
                            , _pmFnAttachments     = pm ^. pmFnAttachments
                            }

  -- Merge the updated references
  let vt = pm ^. pmEntries . mtEntries
      vt' :: ValueTable' PValMd
      vt' = ValueTable { valueNextId   = valueNextId vt
                        , valueEntries  = vte
                        , strtabEntries = strtabEntries vt
                        , valueRelIds   = valueRelIds vt
                        }

      mt' :: MetadataTable' Id
      mt' = MetadataTable { _mtEntries  = pure <$> vt'
                          , _mtNodes    = pm ^. pmEntries . mtNodes
                          , _mtNextNode = pm ^. pmEntries . mtNextNode
                          }

      -- Map.map (Typed (PrimType Metadata) . ValMd)
      pm' :: PartialMetadata Id
      pm' = PartialMetadata { _pmEntries           = mt'
                            , _pmNamedEntries      = pure <$> pne
                            , _pmGlobalAttachments = pure <$> pga
                            , _pmNextName          = pm ^. pmNextName
                            , _pmInstrAttachments  = pm ^. pmInstrAttachments
                            , _pmFnAttachments     = pm ^. pmFnAttachments
                            }

-}
