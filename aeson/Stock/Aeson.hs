{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}    -- the @DeriveStock@ registrations are necessarily orphans
{-# OPTIONS_GHC -Wno-x-partial #-}  -- head/last on aeson method-signature args (always non-empty)

-- | A companion \"solver\" package teaching the @stock@ plugin to derive
-- @ToJSON@ \/ @FromJSON@ (from @aeson@) without being a plugin itself, by
-- registering @instance DeriveStock ToJSON@ and @instance DeriveStock FromJSON@
-- on the "Stock.Derive" SDK.
--
-- The wire format is a simple, self-inverse tagged object —
-- @{ "tag": "Con", "contents": [field₀, field₁, …] }@ — so the two derivers
-- round-trip.  As with @stock-quickcheck@, the @aeson@-specific work
-- (@object@\/@withObject@\/@(.:)@) lives in the ordinary Haskell combinators
-- 'stockToJSON' \/ 'stockParse' \/ 'parseField' below; the synthesized Core just
-- maps each field with @toJSON@ (resp. @parseJSON@) and hands the results to
-- them.
--
-- Downstream: @data T = … deriving (ToJSON, FromJSON) via Stock T@; just depend
-- on @stock-aeson@, no extra @-fplugin@.
--
-- The lifted classes derive the same way: @deriving ToJSON1 via Stock1 F@,
-- @deriving (ToJSON2, FromJSON2) via Stock2 P@.  Bytes match @aeson@'s generic
-- deriving; no @Generic@ at runtime.
module Stock.Aeson
  ( stockToJSON
  , stockToEncoding
  , stockParse
  , parseField
  , liftParseField
  , ToJSON(..)
  , ToJSON1(..)
  , ToJSON2(..)
  , FromJSON(..)
  , FromJSON1(..)
  , FromJSON2(..)
  ) where

import GHC.Plugins
import GHC.Core.Class (Class, classMethods, className)
import GHC.Builtin.Names (applicativeClassName, unpackCStringName)
import GHC.Core.Multiplicity (scaledThing)
import GHC.Tc.Plugin (tcLookupClass, tcLookupId, newWanted, lookupOrig)
import GHC.Tc.Types.Constraint (ctEvExpr, mkNonCanonical)
import GHC.Tc.Types.Evidence (EvTerm(EvExpr))
import GHC.Core.Predicate (mkClassPred)
import Data.Maybe (fromMaybe, isJust)
import Control.Monad (forM, zipWithM)
import Data.Aeson (ToJSON(..), ToJSON1(..), ToJSON2(..), FromJSON(..), FromJSON1(..), FromJSON2(..), Value, object, (.=), withObject, (.:))
import Data.Aeson.Types (Parser)
import Data.Aeson.Encoding (Encoding)
import qualified Data.Aeson.Encoding as E
import qualified Data.Aeson.Key as Key
import Stock.Derive
import Stock.Internal
import Stock.Bifunctor (BiField(..), classifyBiField)

-- These helpers reproduce aeson's @genericToJSON \/ genericParseJSON
-- defaultOptions@ wire format /exactly/ — so @deriving (ToJSON, FromJSON) via
-- Stock T@ is a drop-in for @deriving stock Generic@ + @deriving anyclass
-- (ToJSON, FromJSON)@.  @defaultOptions@ is the @TaggedObject@ encoding with
-- @allNullaryToStringTag = True@ and @tagSingleConstructors = False@, i.e.:
--
--   * all-nullary multi-constructor type  -> the bare string @"Con"@
--   * single-constructor type             -> no tag, just the payload
--   * a record constructor                -> its fields as object keys
--   * a non-record constructor            -> @"contents"@: the bare field
--     (arity 1) or an array (arity 0 or >= 2)
--
-- The synthesizer passes the compile-time shape (single?, all-nullary?, the
-- constructor name, whether it is a record, its field keys / arity) plus the
-- per-field @toJSON@ \/ parser; all the format logic lives here.

-- | Encode one constructor under @defaultOptions@.
stockToJSON :: Bool       -- ^ is the type single-constructor?
            -> Bool       -- ^ is the type all-nullary (and multi-constructor)?
            -> String     -- ^ constructor name
            -> Bool       -- ^ is it a record constructor?
            -> [String]   -- ^ record field keys (empty if not a record)
            -> [Value]    -- ^ the field values
            -> Value
stockToJSON single allNullary name recCon keys fields
  | allNullary = toJSON name
  | single     = payload
  | recCon      = object (("tag" .= name) : recPairs)
  | otherwise  = case fields of
      [] -> object [ "tag" .= name ]
      _  -> object [ "tag" .= name, "contents" .= nonRec ]
  where
    recPairs = zipWith (\k v -> Key.fromString k .= v) keys fields
    payload | recCon     = object recPairs
            | otherwise = nonRec
    nonRec = case fields of { [v] -> v ; vs -> toJSON vs }

-- | Decode under @defaultOptions@: dispatch on the type's shape, recover each
-- constructor's field values in order, and hand them to its builder.
stockParse :: Bool -> Bool -> String
           -> [(String, Bool, [String], Int, [Value] -> Parser a)]
           -> Value -> Parser a
stockParse single allNullary tyName table val
  | allNullary = do t <- parseJSON val ; build t []
  | single     = case table of
      [(_, recCon, keys, ar, b)] -> extractSingle recCon keys ar >>= b
      _                         -> fail (tyName ++ ": expected one constructor")
  | otherwise  = flip (withObject tyName) val \o -> do
      t <- o .: Key.fromString "tag"
      case [ (recCon, keys, ar, b) | (n, recCon, keys, ar, b) <- table, n == t ] of
        ((recCon, keys, ar, b) : _) -> extractTagged o recCon keys ar >>= b
        []                         -> fail (tyName ++ ": unknown tag " ++ t)
  where
    build t vs = case [ b | (n, _, _, _, b) <- table, n == t ] of
      (b : _) -> b vs
      []      -> fail (tyName ++ ": unknown tag " ++ t)
    keyVals o keys = mapM (\k -> o .: Key.fromString k) keys
    extractTagged o recCon keys ar
      | recCon     = keyVals o keys
      | ar == 0   = pure []
      | ar == 1   = (: []) <$> (o .: Key.fromString "contents")
      | otherwise = o .: Key.fromString "contents"
    extractSingle recCon keys ar
      | recCon     = flip (withObject tyName) val \o -> keyVals o keys
      | ar == 0   = pure []
      | ar == 1   = pure [val]
      | otherwise = parseJSON val

-- | Parse the @i@-th recovered field value at its field type.
parseField :: FromJSON a => [Value] -> Int -> Parser a
parseField contents i = case drop i contents of
  (v : _) -> parseJSON v
  []      -> fail "stock-aeson: too few fields"

-- | Like 'parseField' but with the parser supplied (for @liftParseJSON@'s
-- parameter fields): parse the @i@-th value with @p@.
liftParseField :: (Value -> Parser a) -> [Value] -> Int -> Parser a
liftParseField p contents i = case drop i contents of
  (v : _) -> p v
  []      -> fail "stock-aeson: too few fields"

-- | The 'Encoding' twin of 'stockToJSON': the same @defaultOptions@
-- @TaggedObject@ wire format, built with @aeson@'s 'Encoding' combinators so
-- @encode@ (which goes through @toEncoding@ \/ @liftToEncoding@) is byte-for-byte
-- identical to @aeson@'s own generic encoding.
stockToEncoding :: Bool -> Bool -> String -> Bool -> [String] -> [Encoding] -> Encoding
stockToEncoding single allNullary name recCon keys fields
  | allNullary = E.string name
  | single     = payload
  | recCon     = E.pairs (E.pair "tag" (E.string name) `mappend` recSeries)
  | otherwise  = case fields of
      [] -> E.pairs (E.pair "tag" (E.string name))
      _  -> E.pairs (E.pair "tag" (E.string name) `mappend` E.pair "contents" nonRec)
  where
    recSeries = mconcat (zipWith (\k v -> E.pair (Key.fromString k) v) keys fields)
    payload | recCon    = E.pairs recSeries
            | otherwise = nonRec
    nonRec = case fields of { [v] -> v ; vs -> E.list id vs }

-- | A 'Bool' literal in Core.
mkBool :: Bool -> CoreExpr
mkBool b = Var (dataConWorkId (if b then trueDataCon else falseDataCon))

-- | A constructor's record field keys, in field order (empty if not a record).
conKeys :: DataCon -> [String]
conKeys dc = [ occNameString (nameOccName (flSelector fl)) | fl <- dataConFieldLabels dc ]

-- | @toJSON@ under @defaultOptions@: hand each constructor's shape and field
-- @toJSON@s to 'stockToJSON', which reproduces aeson's wire format.
instance DeriveStock ToJSON where
  deriveStock :: Deriver
  deriveStock = Deriver \cls dt -> do
    mTo      <- liftTc (lookupIdMaybe "Stock.Aeson" "stockToJSON")
    unpackId <- liftTc (tcLookupId unpackCStringName)
    case mTo of
      Just toId -> do
        let toJSONSel = classMethod "toJSON" cls
            -- toJSON :: forall a. ToJSON a => a -> Value — read @Value@ off its type
            valueTy   = snd (splitFunTys (snd (splitForAllTyCoVars (idType toJSONSel))))
            mkStr s   = App (Var unpackId) (Lit (mkLitString s))
            strTy     = mkListTy charTy
            cons       = dtCons dt
            singleE    = mkBool (length cons == 1)
            allNullE   = mkBool (length cons > 1 && all (null . conFields) cons)
        x <- fresh (dtVia dt) "x"
        body <- matchSOP dt valueTy (Var x) \_ con fields -> do
          jsons <- forM (zip (conFields con) fields) \(ft, fe) -> do
            d <- field cls ft
            pure (mkApps (Var toJSONSel) [Type ft, d, fe])
          let dc    = conDataCon con
              keys  = conKeys dc
              tag   = mkStr (getOccString dc)
              keysE = mkListExpr strTy (map mkStr keys)
          pure (mkApps (Var toId) [ singleE, allNullE, tag, mkBool (not (null keys))
                                  , keysE, mkListExpr valueTy jsons ])
        classDictWith cls (dtVia dt) [] [(methodIndex "toJSON" cls, mkLams [x] body)]
      _ -> pprPanic "stock-aeson: ToJSON lookups failed" empty

-- | @parseJSON = stockParse \"T\" [(\"Cᵢ\", \\cs -> Cᵢ \<$\> parseField cs 0 \<*\> …)]@.
instance DeriveStock FromJSON where
  deriveStock :: Deriver
  deriveStock = Deriver \cls dt -> do
    mParse   <- liftTc (lookupIdMaybe "Stock.Aeson" "stockParse")
    mField   <- liftTc (lookupIdMaybe "Stock.Aeson" "parseField")
    appCls   <- liftTc (tcLookupClass applicativeClassName)
    unpackId <- liftTc (tcLookupId unpackCStringName)
    case (mParse, mField) of
      (Just parseId, Just fieldId) -> do
        let parseSel = classMethod "parseJSON" cls
            -- parseJSON :: forall a. FromJSON a => Value -> Parser a
            (args, parserA) = splitFunTys (snd (splitForAllTyCoVars (idType parseSel)))
            viaTy    = dtVia dt
            valueTy  = scaledThing (last args)            -- the @Value@ argument
            parserTy = mkTyConTy (tyConAppTyCon parserA)  -- the @Parser@ type constructor
            pureSel  = classMethod "pure" appCls
            apSel    = classMethod "<*>"  appCls
            mkStr s  = App (Var unpackId) (Lit (mkLitString s))
            funChain fts res = foldr mkVisFunTyMany res fts
            contentsTy = mkListTy valueTy
            strTy      = mkListTy charTy
            builderTy  = mkVisFunTyMany contentsTy (mkAppTy parserTy viaTy)
            entryTy    = mkBoxedTupleTy [strTy, boolTy, mkListTy strTy, intTy, builderTy]
            cons       = dtCons dt
            singleE    = mkBool (length cons == 1)
            allNullE   = mkBool (length cons > 1 && all (null . conFields) cons)
        dApp <- field appCls parserTy                     -- Applicative Parser
        entries <- forM cons \con -> do
          let fts = conFields con
          dFs     <- mapM (field cls) fts
          fieldXs <- mapM (\(n, ft) -> fresh ft ("f" ++ show n)) (zip [0 :: Int ..] fts)
          cs      <- fresh contentsTy "cs"
          let conLam  = mkLams fieldXs (injectSOP dt con (map Var fieldXs))  -- fts -> viaTy
              pureLam = mkApps (Var pureSel) [Type parserTy, dApp, Type (funChain fts viaTy), conLam]
              step (acc, j) (ft, d) =
                let pj = mkApps (Var fieldId)
                           [Type ft, d, Var cs, mkUncheckedIntExpr (fromIntegral j)]
                    b  = funChain (drop (j + 1) fts) viaTy
                in (mkApps (Var apSel) [Type parserTy, dApp, Type ft, Type b, acc, pj], j + 1)
              bodyE = fst (foldl step (pureLam, 0 :: Int) (zip fts dFs))
              dc    = conDataCon con
              keys  = conKeys dc
              tag   = mkStr (getOccString dc)
              keysE = mkListExpr strTy (map mkStr keys)
          pure (mkCoreTup [ tag, mkBool (not (null keys)), keysE
                          , mkUncheckedIntExpr (fromIntegral (length fts)), Lam cs bodyE ])
        v <- fresh valueTy "v"
        let impl = mkLams [v]
                     (mkApps (Var parseId)
                        [ Type viaTy, singleE, allNullE
                        , mkStr (showSDocUnsafe (ppr (dtType dt)))
                        , mkListExpr entryTy entries
                        , Var v ])
        classDictWith cls viaTy [] [(methodIndex "parseJSON" cls, impl)]
      _ -> pprPanic "stock-aeson: FromJSON lookups failed (Stock.Aeson helpers)" empty

-- | @liftToJSON@ \/ @liftToEncoding@: parameter fields use the supplied encoder,
-- @h a@ fields @h@'s @liftToJSON@, the rest 'stockToJSON'.  Honours @Override1@.
instance DeriveStock1 ToJSON1 where
  deriveStock1 :: Deriver1
  deriveStock1 = Deriver1 \to1Cls loc wrappedTy f -> do
    mTo      <- lookupIdMaybe "Stock.Aeson" "stockToJSON"
    mToE     <- lookupIdMaybe "Stock.Aeson" "stockToEncoding"
    unpackId <- tcLookupId unpackCStringName
    -- @ToJSON@ shares aeson's (hidden) @Data.Aeson.Types.ToJSON@ module with
    -- @ToJSON1@, so resolve it from the class we are deriving rather than via a
    -- module lookup that the hidden module would defeat.
    toCls    <- tcLookupClass =<< lookupOrig (nameModule (className to1Cls)) (mkTcOcc "ToJSON")
    tcs      <- lookupOvTcs "Override1"
    let mOv1 = ovWrap tcs ; mKeep = ovKeep tcs
        (realF, mMods) = peelOverride1With tcs f
    case (tyConAppTyCon_maybe wrappedTy, tyConAppTyCon_maybe realF, mTo, mToE) of
      (Just st1Tc, Just fTc, Just toId, Just toEId) -> do
        let fixed    = tyConAppArgs realF
            dcons    = tyConDataCons fTc
            coAt t   = coDown1With mOv1 st1Tc wrappedTy f realF t
            ljSel    = classMethod "liftToJSON"     to1Cls
            leSel    = classMethod "liftToEncoding" to1Cls
            toJSel   = classMethod "toJSON"     toCls
            toESel   = classMethod "toEncoding" toCls
            funRes t = snd (splitFunTys (snd (splitForAllTyCoVars t)))
            valueTy  = funRes (idType toJSel)
            encTy    = funRes (idType toESel)
            mkStr s  = App (Var unpackId) (Lit (mkLitString s))
            strTy    = mkListTy charTy
            singleE  = mkBool (length dcons == 1)
            allNullE = mkBool (length dcons > 1 && all ((== 0) . dataConSourceArity) dcons)
        atv <- freshTyVar "a"
        let aTy  = mkTyVarTy atv
            viaA = mkAppTy wrappedTy aTy
            -- one method, flavoured by (result type, assembler, leaf selector for
            -- constants, lifted selector for @h a@ fields).
            buildMethod resTy assembler fnSel liftSel = do
              omitId <- freshId (mkVisFunTyMany aTy boolTy) "omit"
              fnId   <- freshId (mkVisFunTyMany aTy resTy) "f"
              flId   <- freshId (mkVisFunTyMany (mkListTy aTy) resTy) "fl"
              vId    <- freshId viaA "v"
              cb     <- freshId (mkTyConApp fTc (fixed ++ [aTy])) "cb"
              mAltWss <- forM dcons \dc -> do
                let fts  = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [aTy]))
                    keys = conKeys dc
                xs <- zipWithM (\n ft -> freshId ft ("x" ++ show n)) [0 :: Int ..] fts
                mFs <- sequence (zipWith3 (\i ft xi ->
                  case (classifyField atv aTy ft, override1ModWith mKeep mMods i) of
                    (Just FParam, _)      -> pure (Just (App (Var fnId) (Var xi), []))
                    (Just (FApp h), mMod) -> do
                      let m = fromMaybe h mMod
                      ev <- newWanted loc (mkClassPred to1Cls [m])
                      pure (Just ( mkApps (Var liftSel)
                                     [ Type m, ctEvExpr ev, Type aTy
                                     , Var omitId, Var fnId, Var flId
                                     , castReshape (Var xi) (reshapeCo h m aTy) ]
                                 , [mkNonCanonical ev] ))
                    _                     -> do            -- FConst (or unclassifiable): own toJSON
                      ev <- newWanted loc (mkClassPred toCls [ft])
                      pure (Just (mkApps (Var fnSel) [Type ft, ctEvExpr ev, Var xi], [mkNonCanonical ev]))
                  ) [0 :: Int ..] fts xs)
                case sequence mFs of
                  Nothing  -> pure Nothing
                  Just fws -> do
                    let (fvals, wss) = unzip fws
                        call = mkApps (Var assembler)
                                 [ singleE, allNullE, mkStr (getOccString dc)
                                 , mkBool (not (null keys)), mkListExpr strTy (map mkStr keys)
                                 , mkListExpr resTy fvals ]
                    pure (Just (Alt (DataAlt dc) xs call, concat wss))
              case sequence mAltWss of
                Nothing     -> pure Nothing
                Just altWss -> do
                  let (alts, wss) = unzip altWss
                  pure (Just ( mkLams [atv, omitId, fnId, flId, vId]
                                 (destructInner fTc (fixed ++ [aTy]) (Cast (Var vId) (coAt aTy)) cb resTy alts)
                             , concat wss ))
        mLJ <- buildMethod valueTy toId  toJSel ljSel
        mLE <- buildMethod encTy   toEId toESel leSel
        case (mLJ, mLE) of
          (Just (ljImpl, w1), Just (leImpl, w2)) -> do
            dict <- recDictWith to1Cls wrappedTy []
                      [ (methodIndex "liftToJSON" to1Cls, ljImpl)
                      , (methodIndex "liftToEncoding" to1Cls, leImpl) ]
            pure (Just (EvExpr dict, w1 ++ w2))
          _ -> pure Nothing
      _ -> pure Nothing

-- | @liftParseJSON@: parameter fields use the supplied parser, @h a@ fields
-- @h@'s @liftParseJSON@, the rest 'stockParse'.  Honours @Override1@ (parse via
-- the modifier, coerce the @Parser@ back).
instance DeriveStock1 FromJSON1 where
  deriveStock1 :: Deriver1
  deriveStock1 = Deriver1 \fj1Cls loc wrappedTy f -> do
    mParse  <- lookupIdMaybe "Stock.Aeson" "stockParse"
    mField  <- lookupIdMaybe "Stock.Aeson" "parseField"
    mLField <- lookupIdMaybe "Stock.Aeson" "liftParseField"
    unpackId <- tcLookupId unpackCStringName
    appCls  <- tcLookupClass applicativeClassName
    fjCls   <- tcLookupClass =<< lookupOrig (nameModule (className fj1Cls)) (mkTcOcc "FromJSON")
    tcs     <- lookupOvTcs "Override1"
    let mKeep = ovKeep tcs ; mOv1 = ovWrap tcs
        (realF, mMods) = peelOverride1With tcs f
    case (tyConAppTyCon_maybe wrappedTy, tyConAppTyCon_maybe realF, mParse, mField, mLField) of
      (Just st1Tc, Just fTc, Just parseId, Just fieldId, Just lfieldId) -> do
        let dcons = tyConDataCons fTc
        do
          let fixed        = tyConAppArgs realF
              coAt t       = coDown1With mOv1 st1Tc wrappedTy f realF t
              parseSel     = classMethod "parseJSON"     fjCls
              liftParseSel = classMethod "liftParseJSON" fj1Cls
              pureSel      = classMethod "pure" appCls
              apSel        = classMethod "<*>"  appCls
              (pArgs, parserA) = splitFunTys (snd (splitForAllTyCoVars (idType parseSel)))
              valueTy      = scaledThing (last pArgs)
              parserTc     = tyConAppTyCon parserA
              parserTy     = mkTyConTy parserTc
              -- liftParseJSON :: forall f. FromJSON1 f => forall a. Maybe a -> …
              -- strip the outer forall, the @FromJSON1 f@ dict, and the inner forall;
              -- the first value arg is then @Maybe a@.
              afterDict    = snd (splitFunTys (snd (splitForAllTyCoVars (idType liftParseSel))))
              (lpArgs, _)  = splitFunTys (snd (splitForAllTyCoVars afterDict))
              maybeTc      = tyConAppTyCon (scaledThing (head lpArgs))
              mkStr s      = App (Var unpackId) (Lit (mkLitString s))
              strTy        = mkListTy charTy
              funChain ts res = foldr mkVisFunTyMany res ts
              singleE = mkBool (length dcons == 1)
              allNullE= mkBool (length dcons > 1 && all ((== 0) . dataConSourceArity) dcons)
          atv <- freshTyVar "a"
          let aTy        = mkTyVarTy atv
              viaA       = mkAppTy wrappedTy aTy
              parserViaA = mkAppTy parserTy viaA
              contentsTy = mkListTy valueTy
              builderTy  = mkVisFunTyMany contentsTy parserViaA
              entryTy    = mkBoxedTupleTy [strTy, boolTy, mkListTy strTy, intTy, builderTy]
          omittedId <- freshId (mkTyConApp maybeTc [aTy]) "omitted"
          pjId  <- freshId (mkVisFunTyMany valueTy (mkAppTy parserTy aTy)) "pj"
          pjlId <- freshId (mkVisFunTyMany valueTy (mkAppTy parserTy (mkListTy aTy))) "pjl"
          vId   <- freshId valueTy "v"
          dAppEv <- newWanted loc (mkClassPred appCls [parserTy])
          let dApp = ctEvExpr dAppEv
          ews <- forM dcons \dc -> do
            let fts  = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [aTy]))
                keys = conKeys dc
            cs  <- freshId contentsTy "cs"
            xsB <- zipWithM (\n ft -> freshId ft ("x" ++ show n)) [0 :: Int ..] fts
            mPFs <- sequence (zipWith (\i ft ->
              case classifyField atv aTy ft of
                Just FParam   -> pure (Just ( mkApps (Var lfieldId)
                                                [Type aTy, Var pjId, Var cs, mkUncheckedIntExpr (fromIntegral i)]
                                            , [] ))
                Just (FApp h) -> do
                  let mMod = override1ModWith mKeep mMods i        -- Override1: parse via @m@, coerce back
                      m    = fromMaybe h mMod
                  ev <- newWanted loc (mkClassPred fj1Cls [m])
                  let ph  = mkApps (Var liftParseSel)
                              [ Type m, ctEvExpr ev, Type aTy, Var omittedId, Var pjId, Var pjlId ]   -- Value -> Parser (m a)
                      pmf = mkApps (Var lfieldId)
                              [ Type (mkAppTy m aTy), ph, Var cs, mkUncheckedIntExpr (fromIntegral i) ]  -- Parser (m a)
                      pf  = case mMod of
                              Nothing -> pmf
                              Just _  -> Cast pmf (mkTyConAppCo Representational parserTc
                                                     [mkSymCo (reshapeCo h m aTy)])   -- Parser (m a) ~R Parser (h a)
                  pure (Just (pf, [mkNonCanonical ev]))
                _             -> do
                  ev <- newWanted loc (mkClassPred fjCls [ft])
                  pure (Just ( mkApps (Var fieldId)
                                 [Type ft, ctEvExpr ev, Var cs, mkUncheckedIntExpr (fromIntegral i)]
                             , [mkNonCanonical ev] ))
              ) [0 :: Int ..] fts)
            case sequence mPFs of
              Nothing  -> pure Nothing
              Just pfs -> do
                let (parsers, wss) = unzip pfs
                    conE  = mkLams xsB (Cast (mkCoreConApps dc (map Type (fixed ++ [aTy]) ++ map Var xsB))
                                             (mkSymCo (coAt aTy)))            -- fts -> viaA
                    pureL = mkApps (Var pureSel) [Type parserTy, dApp, Type (funChain fts viaA), conE]
                    step (acc, j) p =
                      ( mkApps (Var apSel) [ Type parserTy, dApp, Type (fts !! j)
                                           , Type (funChain (drop (j + 1) fts) viaA), acc, p ]
                      , j + 1 )
                    chain = fst (foldl step (pureL, 0 :: Int) parsers)
                    entry = mkCoreTup [ mkStr (getOccString dc), mkBool (not (null keys))
                                      , mkListExpr strTy (map mkStr keys)
                                      , mkUncheckedIntExpr (fromIntegral (length fts)), Lam cs chain ]
                pure (Just (entry, concat wss))
          case sequence ews of
            Nothing       -> pure Nothing
            Just entryWss -> do
              let (entries, wss) = unzip entryWss
                  impl = mkLams [atv, omittedId, pjId, pjlId, vId]
                           (mkApps (Var parseId)
                              [ Type viaA, singleE, allNullE, mkStr (occNameString (getOccName fTc))
                              , mkListExpr entryTy entries, Var vId ])
              dict <- recDictWith fj1Cls wrappedTy []
                        [ (methodIndex "liftParseJSON" fj1Cls, impl) ]
              pure (Just (EvExpr dict, mkNonCanonical dAppEv : concat wss))
      _ -> pure Nothing

-- | @liftToJSON2@ \/ @liftToEncoding2@: the arity-2 'ToJSON1'.  Honours
-- @Override2@.  No @Generic2@ in aeson, so it coincides with the value encoding
-- when both encoders are @toJSON@.
instance DeriveStock2 ToJSON2 where
  deriveStock2 :: Deriver2
  deriveStock2 = Deriver2 \to2Cls loc wrappedTy p -> do
    mTo  <- lookupIdMaybe "Stock.Aeson" "stockToJSON"
    mToE <- lookupIdMaybe "Stock.Aeson" "stockToEncoding"
    unpackId <- tcLookupId unpackCStringName
    let aesonMod = nameModule (className to2Cls)
    toCls  <- tcLookupClass =<< lookupOrig aesonMod (mkTcOcc "ToJSON")
    to1Cls <- tcLookupClass =<< lookupOrig aesonMod (mkTcOcc "ToJSON1")
    tcs    <- lookupOvTcs "Override2"
    let mOv2 = ovWrap tcs ; mKeep = ovKeep tcs
        (realP, mMods) = peelOverride2With tcs p
    case (tyConAppTyCon_maybe wrappedTy, tyConAppTyCon_maybe realP, mTo, mToE) of
      (Just st2Tc, Just pTc, Just toId, Just toEId) -> do
        let dcons = tyConDataCons pTc
        do
          let fixed      = tyConAppArgs realP
              coAt t1 t2 = coDown2With mOv2 st2Tc wrappedTy p realP t1 t2
              toJSel     = classMethod "toJSON"     toCls
              toESel     = classMethod "toEncoding" toCls
              ljSel      = classMethod "liftToJSON"     to1Cls
              leSel      = classMethod "liftToEncoding" to1Cls
              funRes t   = snd (splitFunTys (snd (splitForAllTyCoVars t)))
              valueTy    = funRes (idType toJSel)
              encTy      = funRes (idType toESel)
              mkStr s    = App (Var unpackId) (Lit (mkLitString s))
              strTy      = mkListTy charTy
              singleE    = mkBool (length dcons == 1)
              allNullE   = mkBool (length dcons > 1 && all ((== 0) . dataConSourceArity) dcons)
          aTv <- freshTyVar "a" ; bTv <- freshTyVar "b"
          let aTy = mkTyVarTy aTv ; bTy = mkTyVarTy bTv
              viaAB = mkAppTy (mkAppTy wrappedTy aTy) bTy
              buildMethod resTy assembler fnSel liftSel = do
                oA  <- freshId (mkVisFunTyMany aTy boolTy) "oA"
                fA  <- freshId (mkVisFunTyMany aTy resTy) "fA"
                flA <- freshId (mkVisFunTyMany (mkListTy aTy) resTy) "flA"
                oB  <- freshId (mkVisFunTyMany bTy boolTy) "oB"
                fB  <- freshId (mkVisFunTyMany bTy resTy) "fB"
                flB <- freshId (mkVisFunTyMany (mkListTy bTy) resTy) "flB"
                vId <- freshId viaAB "v"
                cb  <- freshId (mkTyConApp pTc (fixed ++ [aTy, bTy])) "cb"
                mAltWss <- forM dcons \dc -> do
                  let fts  = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [aTy, bTy]))
                      keys = conKeys dc
                  xs <- zipWithM (\n ft -> freshId ft ("x" ++ show n)) [0 :: Int ..] fts
                  let foldField h elemTy o fn fnl i xi = do      -- @h e@ field; under Override2 reshape @h@ to @m@
                        let m = fromMaybe h (override1ModWith mKeep mMods i)
                        ev <- newWanted loc (mkClassPred to1Cls [m])
                        pure (Just ( mkApps (Var liftSel)
                                       [ Type m, ctEvExpr ev, Type elemTy, Var o, Var fn, Var fnl
                                       , castReshape (Var xi) (reshapeCo h m elemTy) ]
                                   , [mkNonCanonical ev] ))
                  mFs <- sequence (zipWith3 (\i ft xi ->
                    case classifyBiField aTv bTv aTy bTy ft of
                      Just BFA         -> pure (Just (App (Var fA) (Var xi), []))
                      Just BFB         -> pure (Just (App (Var fB) (Var xi), []))
                      Just (BFFoldA h) -> foldField h aTy oA fA flA i xi
                      Just (BFFoldB h) -> foldField h bTy oB fB flB i xi
                      Just BFConst     -> do ev <- newWanted loc (mkClassPred toCls [ft])
                                             pure (Just (mkApps (Var fnSel) [Type ft, ctEvExpr ev, Var xi], [mkNonCanonical ev]))
                      Nothing          -> pure Nothing
                    ) [0 :: Int ..] fts xs)
                  case sequence mFs of
                    Nothing  -> pure Nothing
                    Just fws -> do
                      let (fvals, wss) = unzip fws
                          call = mkApps (Var assembler)
                                   [ singleE, allNullE, mkStr (getOccString dc)
                                   , mkBool (not (null keys)), mkListExpr strTy (map mkStr keys)
                                   , mkListExpr resTy fvals ]
                      pure (Just (Alt (DataAlt dc) xs call, concat wss))
                case sequence mAltWss of
                  Nothing     -> pure Nothing
                  Just altWss -> do
                    let (alts, wss) = unzip altWss
                    pure (Just ( mkLams [aTv, bTv, oA, fA, flA, oB, fB, flB, vId]
                                   (destructInner pTc (fixed ++ [aTy, bTy]) (Cast (Var vId) (coAt aTy bTy)) cb resTy alts)
                               , concat wss ))
          mLJ <- buildMethod valueTy toId  toJSel ljSel
          mLE <- buildMethod encTy   toEId toESel leSel
          case (mLJ, mLE) of
            (Just (lj, w1), Just (le, w2)) -> do
              dict <- recDictWith to2Cls wrappedTy []
                        [ (methodIndex "liftToJSON2" to2Cls, lj)
                        , (methodIndex "liftToEncoding2" to2Cls, le) ]
              pure (Just (EvExpr dict, w1 ++ w2))
            _ -> pure Nothing
      _ -> pure Nothing

-- | @liftParseJSON2@: the arity-2 'liftParseJSON'.  Honours @Override2@.
instance DeriveStock2 FromJSON2 where
  deriveStock2 :: Deriver2
  deriveStock2 = Deriver2 \fj2Cls loc wrappedTy p -> do
    mParse  <- lookupIdMaybe "Stock.Aeson" "stockParse"
    mField  <- lookupIdMaybe "Stock.Aeson" "parseField"
    mLField <- lookupIdMaybe "Stock.Aeson" "liftParseField"
    unpackId <- tcLookupId unpackCStringName
    appCls  <- tcLookupClass applicativeClassName
    let aesonMod = nameModule (className fj2Cls)
    fjCls   <- tcLookupClass =<< lookupOrig aesonMod (mkTcOcc "FromJSON")
    fj1Cls  <- tcLookupClass =<< lookupOrig aesonMod (mkTcOcc "FromJSON1")
    tcs     <- lookupOvTcs "Override2"
    let mOv2 = ovWrap tcs ; mKeep = ovKeep tcs
        (realP, mMods) = peelOverride2With tcs p
    case (tyConAppTyCon_maybe wrappedTy, tyConAppTyCon_maybe realP, mParse, mField, mLField) of
      (Just st2Tc, Just pTc, Just parseId, Just fieldId, Just lfieldId) -> do
        let dcons = tyConDataCons pTc
        do
          let fixed        = tyConAppArgs realP
              coAt t1 t2   = coDown2With mOv2 st2Tc wrappedTy p realP t1 t2
              parseSel     = classMethod "parseJSON"     fjCls
              liftParseSel = classMethod "liftParseJSON" fj1Cls
              lp2Sel       = classMethod "liftParseJSON2" fj2Cls
              pureSel      = classMethod "pure" appCls
              apSel        = classMethod "<*>"  appCls
              (pArgs, parserA) = splitFunTys (snd (splitForAllTyCoVars (idType parseSel)))
              valueTy      = scaledThing (last pArgs)
              parserTc     = tyConAppTyCon parserA
              parserTy     = mkTyConTy parserTc
              afterDict    = snd (splitFunTys (snd (splitForAllTyCoVars (idType lp2Sel))))
              (lpArgs, _)  = splitFunTys (snd (splitForAllTyCoVars afterDict))
              maybeTc      = tyConAppTyCon (scaledThing (head lpArgs))
              mkStr s      = App (Var unpackId) (Lit (mkLitString s))
              strTy        = mkListTy charTy
              funChain ts res = foldr mkVisFunTyMany res ts
              singleE = mkBool (length dcons == 1)
              allNullE= mkBool (length dcons > 1 && all ((== 0) . dataConSourceArity) dcons)
          aTv <- freshTyVar "a" ; bTv <- freshTyVar "b"
          let aTy = mkTyVarTy aTv ; bTy = mkTyVarTy bTv
              viaAB      = mkAppTy (mkAppTy wrappedTy aTy) bTy
              parserViaAB= mkAppTy parserTy viaAB
              contentsTy = mkListTy valueTy
              builderTy  = mkVisFunTyMany contentsTy parserViaAB
              entryTy    = mkBoxedTupleTy [strTy, boolTy, mkListTy strTy, intTy, builderTy]
              vp t       = mkVisFunTyMany valueTy (mkAppTy parserTy t)
          omA <- freshId (mkTyConApp maybeTc [aTy]) "omA"
          pjA <- freshId (vp aTy) "pjA" ; pjlA <- freshId (vp (mkListTy aTy)) "pjlA"
          omB <- freshId (mkTyConApp maybeTc [bTy]) "omB"
          pjB <- freshId (vp bTy) "pjB" ; pjlB <- freshId (vp (mkListTy bTy)) "pjlB"
          vId <- freshId valueTy "v"
          dAppEv <- newWanted loc (mkClassPred appCls [parserTy])
          let dApp = ctEvExpr dAppEv
          ews <- forM dcons \dc -> do
            let fts  = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [aTy, bTy]))
                keys = conKeys dc
            cs  <- freshId contentsTy "cs"
            xsB <- zipWithM (\n ft -> freshId ft ("x" ++ show n)) [0 :: Int ..] fts
            mPFs <- sequence (zipWith (\i ft ->
              let lifted h elemTy om pj pjl = do      -- @h e@ field; Override2 parses via @m@, coerces to @h e@
                    let mMod = override1ModWith mKeep mMods i
                        m    = fromMaybe h mMod
                    ev <- newWanted loc (mkClassPred fj1Cls [m])
                    let ph  = mkApps (Var liftParseSel) [Type m, ctEvExpr ev, Type elemTy, Var om, Var pj, Var pjl]
                        pmf = mkApps (Var lfieldId) [Type (mkAppTy m elemTy), ph, Var cs, mkUncheckedIntExpr (fromIntegral i)]
                        pf  = case mMod of
                                Nothing -> pmf
                                Just _  -> Cast pmf (mkTyConAppCo Representational parserTc
                                                       [mkSymCo (reshapeCo h m elemTy)])
                    pure (Just (pf, [mkNonCanonical ev]))
              in case classifyBiField aTv bTv aTy bTy ft of
                Just BFA         -> pure (Just (mkApps (Var lfieldId) [Type aTy, Var pjA, Var cs, mkUncheckedIntExpr (fromIntegral i)], []))
                Just BFB         -> pure (Just (mkApps (Var lfieldId) [Type bTy, Var pjB, Var cs, mkUncheckedIntExpr (fromIntegral i)], []))
                Just (BFFoldA h) -> lifted h aTy omA pjA pjlA
                Just (BFFoldB h) -> lifted h bTy omB pjB pjlB
                Just BFConst     -> do ev <- newWanted loc (mkClassPred fjCls [ft])
                                       pure (Just (mkApps (Var fieldId) [Type ft, ctEvExpr ev, Var cs, mkUncheckedIntExpr (fromIntegral i)], [mkNonCanonical ev]))
                Nothing          -> pure Nothing
              ) [0 :: Int ..] fts)
            case sequence mPFs of
              Nothing  -> pure Nothing
              Just pfs -> do
                let (parsers, wss) = unzip pfs
                    conE  = mkLams xsB (Cast (mkCoreConApps dc (map Type (fixed ++ [aTy, bTy]) ++ map Var xsB))
                                             (mkSymCo (coAt aTy bTy)))
                    pureL = mkApps (Var pureSel) [Type parserTy, dApp, Type (funChain fts viaAB), conE]
                    step (acc, j) pe =
                      ( mkApps (Var apSel) [ Type parserTy, dApp, Type (fts !! j)
                                           , Type (funChain (drop (j + 1) fts) viaAB), acc, pe ]
                      , j + 1 )
                    chain = fst (foldl step (pureL, 0 :: Int) parsers)
                    entry = mkCoreTup [ mkStr (getOccString dc), mkBool (not (null keys))
                                      , mkListExpr strTy (map mkStr keys)
                                      , mkUncheckedIntExpr (fromIntegral (length fts)), Lam cs chain ]
                pure (Just (entry, concat wss))
          case sequence ews of
            Nothing       -> pure Nothing
            Just entryWss -> do
              let (entries, wss) = unzip entryWss
                  impl = mkLams [aTv, bTv, omA, pjA, pjlA, omB, pjB, pjlB, vId]
                           (mkApps (Var parseId)
                              [ Type viaAB, singleE, allNullE, mkStr (occNameString (getOccName pTc))
                              , mkListExpr entryTy entries, Var vId ])
              dict <- recDictWith fj2Cls wrappedTy []
                        [ (methodIndex "liftParseJSON2" fj2Cls, impl) ]
              pure (Just (EvExpr dict, mkNonCanonical dAppEv : concat wss))
      _ -> pure Nothing

-- | The position of a class method by source name.
methodIndex :: String -> Class -> Int
methodIndex name cls =
  case [ i | (i, m) <- zip [0 :: Int ..] (classMethods cls)
           , occNameString (occName m) == name ] of
    (i : _) -> i
    []      -> 0
