
unnamedEntries :: forall f. (Applicative f)
               => PartialMetadata (Compose (LookupMd f) f)
               -> Compose (LookupMd f) f ([PartialUnnamedMd], [PartialUnnamedMd])
unnamedEntries pm =
  (\entries -> partitionEithers . mapMaybe (resolveNode entries) . Map.toList)
  <$> seqMap (valueEntries $ pm ^. pmEntries . mtEntries)
  <*> seqMap (pm ^. pmEntries . mtNodes)
  where
    -- TODO: is this silently eating errors with metadata that's not in the
    -- value table (by passing along the 'Nothing' from the Map lookup)?
    --
    -- NB: the bind (=<<) happens in 'Maybe'.
    resolveNode :: Map Int (Typed PValue) -- ^ mtEntries
                -> (Int, (Bool, Bool, Int)) -- ^ mtNodes
                -> Maybe (Either PartialUnnamedMd PartialUnnamedMd)
    resolveNode entries (ref, (fnLocal, isDistinct, ix)) =
      (if fnLocal then Left else Right) <$>
        (mkPartialUnnamedMd ix isDistinct =<< Map.lookup ref entries)

    mkPartialUnnamedMd :: Int -> Bool -> Typed PValue -> Maybe PartialUnnamedMd
    mkPartialUnnamedMd ix d =
      \case
        Typed{ typedValue = ValMd v } ->
          Just PartialUnnamedMd
            { pumIndex    = ix
            , pumValues   = v
            , pumDistinct = d
            }
        _ -> Nothing
