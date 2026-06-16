{-# LANGUAGE CPP #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DerivingVia #-}
{-# OPTIONS_GHC -Wno-x-partial -Wno-incomplete-uni-patterns -Wno-unused-imports #-}
-- | Shared substrate for the Stock plugin: environments, the representation
-- EDSL, Core/dictionary builders, the variance walk, and the @Solver@ monoid.
module Stock.Internal (module Stock.Internal) where
-- Most names below (data-con/type builders, coercion builders, occ-name
-- helpers, …) are re-exported by 'GHC.Plugins', so we only import explicitly
-- the ones it does not provide.
import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Plugin
import GHC.Tc.Types
import GHC.Tc.Types.Constraint
#if MIN_VERSION_ghc(9,12,0)
import GHC.Tc.Types.CtLoc (CtLoc)
#else
import GHC.Tc.Types.Constraint (CtLoc)
#endif
import GHC.Tc.Types.Evidence
import GHC.Tc.Utils.Monad (addErrTc)
import GHC.Tc.Errors.Types (mkTcRnUnknownMessage)
import GHC.Types.Error (mkPlainError, noHints)
import GHC.Core.Class (Class, className, classMethods, classOpItems, classTyCon)
import GHC.Core.Predicate (classifyPredType, Pred(ClassPred), mkClassPred)
#if MIN_VERSION_ghc(9,14,0)
import GHC.Core.Predicate (mkReprEqPred)
#else
import GHC.Core.Predicate (mkReprPrimEqPred)
#endif
import GHC.Builtin.Types (promotedConsDataCon, promotedNilDataCon, unitTy)
import GHC.Builtin.Types.Prim (intPrimTy)
import GHC.Builtin.PrimOps (PrimOp(TagToEnumOp))
import GHC.Builtin.PrimOps.Ids (primOpId)
import GHC.Builtin.Names ( eqClassName, ordClassName, appendName
                         , enumClassName, mapName, numClassName
                         , enumFromToName, enumFromThenToName
                         , eqStringName
                         , genClassName, repTyConName, u1TyConName, k1TyConName
                         , prodTyConName, sumTyConName
                         , monoidClassName, foldableClassName, functorClassName
                         , semigroupClassName, monadClassName )
import Stock.Compat ( gHC_INTERNAL_SHOW, gHC_INTERNAL_READ
                    , gHC_INTERNAL_LIST, gHC_INTERNAL_GENERICS
                    , tEXT_READPREC, tEXT_READ_LEX )
import GHC.Core.Reduction (mkReduction)
import GHC.Core.TyCo.Rep (UnivCoProvenance(PluginProv))
import GHC.Rename.Fixity (lookupFixityRn)
import GHC.Types.Fixity (Fixity(..), defaultFixity, FixityDirection(..))
import GHC.Types.SourceText (SourceText(NoSourceText))
import GHC.Core.DataCon (dataConSrcBangs, dataConImplBangs, HsSrcBang(..), HsImplBang(..), SrcStrictness(..), SrcUnpackedness(..))
import GHC.Core.TyCo.Compare (eqType)
import GHC.Core.Multiplicity (scaledThing)
import GHC.Core.SimpleOpt (defaultSimpleOpts)
import GHC.Core.Unfold.Make (mkInlineUnfoldingWithArity)
import GHC.Core.InstEnv (classInstances, is_dfun, is_tys)
import GHC.Runtime.Loader (getValueSafely)
import Stock.Derive
import Data.Maybe (catMaybes, fromJust, isJust, fromMaybe, listToMaybe)
import Data.List (zipWith4)
import Data.Traversable (for)
import qualified Data.Monoid as Mon (Alt(..))  -- 'Alt' clashes with GHC.Core's case-alt 'Alt'
import Stock.Trans (MaybeT(..))
import Control.Monad (zipWithM, unless, guard)
import Data.IORef (IORef, newIORef, readIORef, modifyIORef')
-- | Entities looked up once for @Generic@ synthesis: the @Generic@ class, the
-- @Rep@ family, and the representation pieces @U1@, @K1@/@Rec0@ and @:*:@.
data GenEnv = GenEnv
  { geStock   :: Maybe TyCon  -- ^ our @Stock.Stock@ ('Nothing' if not in scope)
  , geStock1  :: Maybe TyCon  -- ^ our @Stock.Stock1@
  , geStock2  :: Maybe TyCon  -- ^ our @Stock.Stock2@
  , geWitness :: Maybe Class -- ^ @Stock.Derive.DeriveStock@ (for discovered derivers)
  , geGen     :: Class
  , geRepTc   :: TyCon
  , geU1Tc    :: TyCon
  , geK1Tc    :: TyCon
  , geProdTc  :: TyCon
  , geProdDc  :: DataCon
  , geSumTc   :: TyCon       -- ^ @:+:@ (for sum-type @Rep@s)
  , geMeta    :: MetaEnv     -- ^ @M1@ + promoted @Meta@ pieces (for metadata layers)
  , geGen1    :: Gen1Env     -- ^ @Generic1@ / @Rep1@ pieces
  , geRTy     :: Type     -- ^ the @R@ tag (for @Rec0 = K1 R@)
  , geOverride :: Maybe TyCon  -- ^ @Stock.Override.Override@ ('Nothing' if not in scope)
  , geAssign   :: Maybe TyCon  -- ^ @Stock.Override.(:=)@ — the config-entry marker
  , geAt       :: Maybe TyCon  -- ^ @Stock.Override.At@ — the positional selector marker
  , geKeep     :: Maybe TyCon  -- ^ @Stock.Override.Keep@ — the positional no-op (@_@) marker
  , geArrow    :: Maybe TyCon  -- ^ @Stock.Override.(-->)@ — the path-addressing marker
  , geWitness1 :: Maybe Class  -- ^ @Stock.Derive.DeriveStock1@ (lifted discovered derivers)
  , geWitness2 :: Maybe Class  -- ^ @Stock.Derive.DeriveStock2@ (bi-lifted discovered derivers)
  , geOverride2 :: Maybe TyCon -- ^ @Stock.Override.Override2@ — per-field override at the @Stock2@ level
  , geOverride1 :: Maybe TyCon -- ^ @Stock.Override.Override1@ — per-field override at the @Stock1@ level
  }

-- | The @M1@ newtype and the promoted @Meta@ pieces needed to build the
-- @D1@/@C1@/@S1@ metadata layers of a faithful (nominal) @Rep@.
data MetaEnv = MetaEnv
  { meM1          :: TyCon        -- ^ @M1@
  , meD, meC, meS :: Type        -- ^ the @D@\/@C@\/@S@ tags (kind @Type@)
  , meMetaData    :: TyCon        -- ^ promoted @'MetaData@
  , meMetaCons    :: TyCon        -- ^ promoted @'MetaCons@
  , meMetaSel     :: TyCon        -- ^ promoted @'MetaSel@
  , mePrefixI     :: Type         -- ^ @'PrefixI@
  , meInfixI      :: TyCon        -- ^ promoted @'InfixI@ (assoc → nat → FixityI)
  , meLeftAssoc, meRightAssoc, meNotAssoc :: Type  -- ^ promoted @Associativity@
  , meNoUnpack, meSrcNoUnpack, meSrcUnpack :: Type -- ^ promoted @SourceUnpackedness@
  , meNoStrict, meSrcLazy, meSrcStrict     :: Type -- ^ promoted @SourceStrictness@
  , meDecidedLazy, meDecidedStrict, meDecidedUnpack :: Type -- ^ promoted @DecidedStrictness@
  , meJustSym     :: TyCon        -- ^ promoted @'Just@ \@Symbol
  , meNothingSym  :: Type         -- ^ @'Nothing \@Symbol@
  }

-- | @Generic1@ entities: the class, the @Rep1@ family, and the parameter-aware
-- representation pieces @Par1@\/@Rec1@\/@(:.:)@.
data Gen1Env = Gen1Env
  { g1RepTc  :: TyCon   -- ^ @Rep1@
  , g1Par1Tc :: TyCon   -- ^ @Par1@ (the bare parameter)
  , g1Rec1Tc :: TyCon   -- ^ @Rec1@ (@g a@)
  , g1CompTc :: TyCon   -- ^ @(:.:)@ (composition, @f (g a)@)
  }

-- | Plugin state: error-message dedup set + the @Generic@ entities.
data PluginState = PluginState
  { psSeen :: IORef [String]
  , psGen  :: GenEnv
  }

-- | Short-circuiting conjunction of @Bool@-valued Core expressions — reads like
-- @and [b0, b1, …]@ but builds the nested @case e of { False -> False; True ->
-- … }@ chain, the same Core a derived @&&@ chain produces: no list, no
-- allocation, byte-identical to stock deriving.
andE :: [CoreExpr] -> TcPluginM CoreExpr
andE []     = pure (Var (dataConWorkId trueDataCon))
andE [a]    = pure a
andE (a:as) = do
  r   <- andE as
  scr <- freshId boolTy "c"
  pure (Case a scr boolTy [ Alt (DataAlt falseDataCon) [] (Var (dataConWorkId falseDataCon))
                          , Alt (DataAlt trueDataCon)  [] r ])

lookupTyConMaybe :: String -> String -> TcPluginM (Maybe TyCon)
lookupTyConMaybe modName occ = do
  res <- findImportedModule (mkModuleName modName) NoPkgQual
  case res of
    Found _ m -> Just <$> (lookupOrig m (mkTcOcc occ) >>= tcLookupTyCon)
    _         -> pure Nothing

-- | Look up the @M1@ + promoted @Meta@ entities for metadata layers.
lookupMetaEnv :: TcPluginM MetaEnv
lookupMetaEnv = do
  let gTc occ = lookupOrig gHC_INTERNAL_GENERICS (mkTcOcc occ)   >>= tcLookupTyCon
      gDc occ = lookupOrig gHC_INTERNAL_GENERICS (mkDataOcc occ) >>= tcLookupDataCon
      promTy  = fmap (mkTyConTy . promoteDataCon) . gDc
  m1  <- gTc "M1"
  dT  <- mkTyConTy <$> gTc "D" ; cT <- mkTyConTy <$> gTc "C" ; sT <- mkTyConTy <$> gTc "S"
  md  <- promoteDataCon <$> gDc "MetaData"
  mc  <- promoteDataCon <$> gDc "MetaCons"
  ms  <- promoteDataCon <$> gDc "MetaSel"
  pfx <- promTy "PrefixI"
  inI <- promoteDataCon <$> gDc "InfixI"
  la  <- promTy "LeftAssociative" ; ra <- promTy "RightAssociative" ; na <- promTy "NotAssociative"
  nu  <- promTy "NoSourceUnpackedness" ; snu <- promTy "SourceNoUnpack" ; su <- promTy "SourceUnpack"
  ns  <- promTy "NoSourceStrictness"   ; sl  <- promTy "SourceLazy"     ; ss <- promTy "SourceStrict"
  dl  <- promTy "DecidedLazy" ; ds <- promTy "DecidedStrict" ; du <- promTy "DecidedUnpack"
  pure MetaEnv { meM1 = m1, meD = dT, meC = cT, meS = sT
               , meMetaData = md, meMetaCons = mc, meMetaSel = ms
               , mePrefixI = pfx, meInfixI = inI
               , meLeftAssoc = la, meRightAssoc = ra, meNotAssoc = na
               , meNoUnpack = nu, meSrcNoUnpack = snu, meSrcUnpack = su
               , meNoStrict = ns, meSrcLazy = sl, meSrcStrict = ss
               , meDecidedLazy = dl, meDecidedStrict = ds, meDecidedUnpack = du
               , meJustSym = promotedJustDataCon
               , meNothingSym = mkTyConApp promotedNothingDataCon [typeSymbolKind] }

-- | Look up the @Generic1@ / @Rep1@ entities.
lookupGen1Env :: TcPluginM Gen1Env
lookupGen1Env = do
  let gTc occ = lookupOrig gHC_INTERNAL_GENERICS (mkTcOcc occ) >>= tcLookupTyCon
  Gen1Env <$> gTc "Rep1" <*> gTc "Par1" <*> gTc "Rec1" <*> gTc ":.:"

-- | Look up a class by module + name, 'Nothing' if its module isn't available.
lookupClassMaybe :: String -> String -> TcPluginM (Maybe Class)
lookupClassMaybe modName occ = do
  res <- findImportedModule (mkModuleName modName) NoPkgQual
  case res of
    Found _ m -> Just <$> (lookupOrig m (mkTcOcc occ) >>= tcLookupClass)
    _         -> pure Nothing

-- | Look up a term-level identifier (a function\/value) by module + name,
-- 'Nothing' if its module isn't available — for companion derivers that need to
-- reference a library function (e.g. QuickCheck's @oneof@).
lookupIdMaybe :: String -> String -> TcPluginM (Maybe Id)
lookupIdMaybe modName occ = do
  res <- findImportedModule (mkModuleName modName) NoPkgQual
  case res of
    Found _ m -> Just <$> (lookupOrig m (mkVarOcc occ) >>= tcLookupId)
    _         -> pure Nothing

-- | Rewrite @Rep (Stock T)@ to its structural representation.  The coercion is
-- a plugin-asserted univ coercion (there is no real @Generic@ axiom); the
-- @from@/@to@ we synthesize use the same assertion, so the two cohere.  We only
-- handle single-constructor types (products) so far.
repData :: GenEnv -> [[Type]] -> Type
repData gen [fts] = repStruct gen fts
repData gen ftss  = foldBal sumOf (map (repStruct gen) ftss) where 
  sumOf :: Type -> Type -> Type
  sumOf f g = mkTyConApp (geSumTc gen) [liftedTypeKind, f, g]

-- | The /faithful/ @Rep@ with metadata layers: @D1 meta (C1 meta (S1 meta Rec0
-- … :*: …) :+: …)@ — byte-identical in shape to GHC's stock @Rep@ (balanced
-- @:+:@/@:*:@, @M1@ wrappers carrying promoted @Meta@).  Used as the rewrite
-- target; the value-level @from@\/@to@ build the un-@M1@ 'repData' value and
-- bridge with a representational coercion (the @M1@s are newtypes).
-- | @Rec0 t = K1 R t@ — the field representation for a constant (and for every
-- field in plain @Generic@).
rec0Of :: GenEnv -> Type -> Type
rec0Of gen t = mkTyConApp (geK1Tc gen) [liftedTypeKind, geRTy gen, t]

repMeta :: GenEnv -> (DataCon -> Type) -> Type -> [DataCon] -> Type
repMeta gen fixOf innerTy dcons =
  repMetaWith gen fixOf (rec0Of gen) innerTy [ (dc, fieldTysAt innerTy dc) | dc <- dcons ]

-- | 'repMeta' with explicit per-constructor field types — the @Generic@ leaves
-- carry these (the /modifier/ types under an @Override@, the real types
-- otherwise).  Pairs with the @from@\/@to@ that 'Stock.Generic' builds.
repMetaFts :: GenEnv -> (DataCon -> Type) -> Type -> [(DataCon, [Type])] -> Type
repMetaFts gen fixOf = repMetaWith gen fixOf (rec0Of gen)

-- | 'repMeta' generalised over the per-field leaf representation: @Generic@
-- uses @Rec0@; @Generic1@ uses @Par1@\/@Rec1@\/@(:.:)@ ('rep1Field').  Each
-- constructor comes with the field types its leaves should carry.
repMetaWith :: GenEnv -> (DataCon -> Type) -> (Type -> Type) -> Type -> [(DataCon, [Type])] -> Type
repMetaWith gen fixOf leaf innerTy cons =
  d1 (metaData innerTc) (foldBal sumTy (map conRep cons)) where
  me      = geMeta gen
  innerTc = tyConAppTyCon innerTy
  kTy     = liftedTypeKind
  m1 i c f = mkTyConApp (meM1 me) [kTy, i, c, f]
  d1 = m1 (meD me) ; c1 = m1 (meC me) ; s1 = m1 (meS me)
  sumTy  a b = mkTyConApp (geSumTc gen)  [kTy, a, b]
  prodTy a b = mkTyConApp (geProdTc gen) [kTy, a, b]
  u1     = mkTyConApp (geU1Tc gen) [kTy]
  strLit = mkStrLitTy . fsLit
  boolT b = mkTyConTy (if b then promotedTrueDataCon else promotedFalseDataCon)
  metaData tc = mkTyConApp (meMetaData me)
                  [ strLit (occNameString (nameOccName (tyConName tc)))
                  , strLit (moduleNameString (moduleName modu))
                  , strLit (unitString (moduleUnit modu))
                  , boolT (isNewTyCon tc) ]
    where modu = nameModule (tyConName tc)
  -- MetaCons carries the constructor's FIXITY ('Infix assoc prec for an infix
  -- constructor, else 'PrefixI) — supplied by the (monadic) 'mkFixOf'.
  metaCons dc = mkTyConApp (meMetaCons me)
                  [ strLit (occNameString (getOccName dc))
                  , fixOf dc
                  , boolT (not (null (dataConFieldLabels dc))) ]
  -- MetaSel carries the field's real source/decided strictness.
  metaSel mnm (suT, ssT, dsT) = mkTyConApp (meMetaSel me)
                  [ maybe (meNothingSym me)
                          (\nm -> mkTyConApp (meJustSym me) [typeSymbolKind, strLit nm]) mnm
                  , suT, ssT, dsT ]
  -- derive (SourceUnpackedness, SourceStrictness, DecidedStrictness) from the
  -- DECIDED bang ('HsImplBang' is stable across GHC versions, unlike 'HsSrcBang'
  -- which changed shape thrice): an unannotated field is lazy; a @!@ field is
  -- source-strict + decided-strict; an UNPACK field is source-unpack (the rare
  -- explicit @~@ lazy annotation is the one case this can't tell from plain).
  selStr dc i = case if i < length implB then implB !! i else HsLazy of
      HsLazy     -> (meNoUnpack me,  meNoStrict me,  meDecidedLazy me)
      HsStrict _ -> (meNoUnpack me,  meSrcStrict me, meDecidedStrict me)
      HsUnpack _ -> (meSrcUnpack me, meSrcStrict me, meDecidedUnpack me)
    where implB = dataConImplBangs dc
  conRep (dc, fts) = c1 (metaCons dc) prod
    where labels = dataConFieldLabels dc
          nameAt i | null labels = Nothing
                   | otherwise   = Just (occNameString (nameOccName (flSelector (labels !! i))))
          prod = case fts of
                   [] -> u1
                   _  -> foldBal prodTy
                           [ s1 (metaSel (nameAt i) (selStr dc i)) (leaf ft)
                           | (i, ft) <- zip [0 :: Int ..] fts ]

-- 'Fixity' lost its leading 'SourceText' in GHC 9.12 (2-arg from 9.12 on).
fixityParts :: Fixity -> (Int, FixityDirection)
#if MIN_VERSION_ghc(9,12,0)
fixityParts (Fixity p d)   = (p, d)
#else
fixityParts (Fixity _ p d) = (p, d)
#endif

-- | The per-constructor MetaCons fixity meta ('Infix assoc prec / 'PrefixI),
-- precomputed (it needs the renamer's fixity environment).
conFixityTy :: MetaEnv -> DataCon -> TcPluginM Type
conFixityTy me dc
  | dataConIsInfix dc = do
      fx <- unsafeTcPluginTcM (lookupFixityRn (dataConName dc))
      let (prec, dir) = fixityParts fx
          assoc = case dir of InfixL -> meLeftAssoc me; InfixR -> meRightAssoc me; InfixN -> meNotAssoc me
      pure (mkTyConApp (meInfixI me) [assoc, mkNumLitTy (fromIntegral prec)])
  | otherwise = pure (mePrefixI me)

-- | A pure fixity lookup over a fixed constructor set (for 'repMetaWith').
mkFixOf :: MetaEnv -> [DataCon] -> TcPluginM (DataCon -> Type)
mkFixOf me dcs = do
  tys <- mapM (conFixityTy me) dcs
  let m = zip (map getUnique dcs) tys
  pure (\dc -> fromMaybe (mePrefixI me) (lookup (getUnique dc) m))

-- | The structural @Rep@ type for a single constructor with the given field
-- types: @U1@ when there are no fields, otherwise a /balanced/ @:*:@ tree of
-- @Rec0 field@ (matching GHC's @foldBal@ nesting).  No @M1@ metadata layers
-- yet — this is a valid representation that @Generically@ can use, just not
-- byte-identical to stock's.
repStruct :: GenEnv -> [Type] -> Type
repStruct gen []  = mkTyConApp (geU1Tc gen) [liftedTypeKind]    -- U1 @Type
repStruct gen fts = foldBal prodOf (map rec0 fts) where

  rec0 t    = mkTyConApp (geK1Tc gen)   [liftedTypeKind, geRTy gen, t]  -- K1 @Type R t
  prodOf f g = mkTyConApp (geProdTc gen) [liftedTypeKind, f, g]         -- (f :*: g) @Type

-- | Classify a field for @Rep1@: the bare parameter @a@ ⇒ @Par1@; @g a@ with
-- @g@ closed ⇒ @Rec1 g@; a field without the parameter ⇒ @Rec0@ (constant).
-- 'Nothing' for shapes we don't yet handle (composition @f (g a)@, or the
-- parameter in a position other than the last argument of a closed functor).
rep1Field :: GenEnv -> TyVar -> Type -> Maybe Type
rep1Field gen aTv ft
  | ft `eqType` aTy                          = Just par1
  | not (aTv `elemVarSet` tyCoVarsOfType ft) = Just (rec0Of gen ft)
  | Just (h, larg) <- splitAppTy_maybe ft
  , not (aTv `elemVarSet` tyCoVarsOfType h)  =
      if larg `eqType` aTy then Just (rec1 h)             -- @h a@      ⇒ Rec1 h
      else comp h <$> rep1Field gen aTv larg              -- @h (g..a)@ ⇒ h :.: <inner>
  | otherwise                                = Nothing
  where
    g1   = geGen1 gen ; kTy = liftedTypeKind ; aTy = mkTyVarTy aTv
    par1 = mkTyConTy (g1Par1Tc g1)
    rec1 h     = mkTyConApp (g1Rec1Tc g1) [kTy, h]
    comp h inr = mkTyConApp (g1CompTc g1) [kTy, kTy, h, inr]

-- | A balanced binary fold (GHC's @foldBal@): splits the list in half and
-- recurses, giving @(a \`op\` b) \`op\` (c \`op\` d)@ rather than a right-nested
-- chain.  Precondition: non-empty.
foldBal :: (a -> a -> a) -> [a] -> a
foldBal _  [x] = x
foldBal op xs  = let (l, r) = splitAt (length xs `div` 2) xs
                 in op (foldBal op l) (foldBal op r)

-- | Try to solve every wanted constraint by direct synthesis.  Synthesis may
-- emit further wanted constraints (e.g. @Eq@ on a field type), which we hand
-- back to the solver alongside our solutions.
type Attempt = (Maybe (EvTerm, Ct), [Ct], [Ct])

-- ---------------------------------------------------------------------------
-- A little EDSL describing the datatype representation a Stock-wrapped type
-- exposes.  Everything the synthesizers need to inspect lives here, so the
-- "is this something we can build an instance for, and what does it look like"
-- question is answered in exactly one place.
-- ---------------------------------------------------------------------------

-- | One constructor's representation: the constructor itself and its field
-- types (instantiated at the inner type's arguments).
data ConInfo = ConInfo
  { ciCon      :: DataCon
  , ciFields   :: [Type]        -- ^ field types the synthesizer sees (modifier types if overridden)
  , ciFieldCos :: [Coercion]    -- ^ per field, @realFieldType ~R ciFields!!i@ (Refl if not overridden)
  }

-- | The representation of @Stock Inner@: the inner type, the newtype-unwrapping
-- coercion @wrapped ~R inner@, and the constructors.
data Repr = Repr
  { rInner :: Type
  , rCo    :: Coercion
  , rCons  :: [ConInfo]
  }

-- | Recognise @Stock Inner@ where @Stock@ is exactly /our/ wrapper newtype
-- (identified by 'TyCon', not by name — so an unrelated user type called
-- @Stock@ is never touched) and @Inner@ is a concrete algebraic type, and read
-- off its representation.  Returns 'Nothing' for anything we don't own or can't
-- analyse (including when our @Stock@ couldn't be located, i.e. @ourStock@ is
-- 'Nothing').
mkRepr :: Maybe TyCon -> Type -> Maybe Repr
mkRepr ourStock wrappedTy = do
  ourTc   <- ourStock
  stockTc <- tyConAppTyCon_maybe wrappedTy
  guard (stockTc == ourTc)
  innerTy <- case tyConAppArgs wrappedTy of { (a:_) -> Just a; _ -> Nothing }
  innerTc <- tyConAppTyCon_maybe innerTy
  let dcons = tyConDataCons innerTc
  guard (not (null dcons))
  let co = mkUnbranchedAxInstCo Representational
             (newTyConCo stockTc) (tyConAppArgs wrappedTy) []
      cons = [ ConInfo dc fts (map mkRepReflCo fts)
             | dc <- dcons, let fts = fieldTysAt innerTy dc ]
  pure (Repr innerTy co cons)

-- | A plugin-asserted coercion (there is no real axiom; the plugin vouches for
-- the representational equality).  'mkUnivCo' gained a @[Coercion]@ dependency
-- argument in GHC 9.12, so this wrapper keeps call sites version-agnostic.
mkStockCo :: UnivCoProvenance -> Role -> Type -> Type -> Coercion
#if MIN_VERSION_ghc(9,12,0)
mkStockCo prov = mkUnivCo prov []
#else
mkStockCo = mkUnivCo
#endif

-- | The @Override(1\/2)@ field reshape coercion @h t ~R m t@ — 'Refl' when the
-- field is not overridden (@h == m@), else the plugin-asserted representational
-- equality.  Shared by every synthesizer that reshapes a functor field.
reshapeCo :: Type -> Type -> Type -> Coercion
reshapeCo h m t
  | h `eqType` m = mkRepReflCo (mkAppTy h t)
  | otherwise    = mkStockCo (PluginProv "stock") Representational (mkAppTy h t) (mkAppTy m t)

-- | Cast by a reshape coercion, skipping the no-op 'Refl' (so non-overridden
-- fields stay syntactically untouched and the emitted Core is byte-identical).
castReshape :: CoreExpr -> Coercion -> CoreExpr
castReshape e co = if isReflCo co then e else Cast e co

-- ---------------------------------------------------------------------------
-- Override: per-field deriving modifiers (see docs/override-design.md)
-- ---------------------------------------------------------------------------

-- | Peel @Override1 cfg f@ to the real constructor and its per-field positional
-- modifiers (single inner list); a non-overridden @f@ gives @(f, Nothing)@.
peelOverride1 :: GenEnv -> Type -> (Type, Maybe [Type])
peelOverride1 gen = peelOverride1With (ovTcsGen "Override1" gen)

-- | The @Override@-config 'TyCon's a config decoder needs.  Bundled so the
-- satellite 'Deriver1'\/'Deriver2's (which have no 'GenEnv') can pass them.
data OvTcs = OvTcs
  { ovWrap   :: Maybe TyCon   -- ^ @Override1@ \/ @Override2@
  , ovKeep   :: Maybe TyCon   -- ^ @Keep@
  , ovArrow  :: Maybe TyCon   -- ^ @-->@
  , ovAssign :: Maybe TyCon   -- ^ @:=@
  , ovAt     :: Maybe TyCon   -- ^ @At@
  }

-- | The bundle, from a 'GenEnv' (for the built-in synthesizers).
ovTcsGen :: String -> GenEnv -> OvTcs
ovTcsGen wrap gen = OvTcs
  (if wrap == "Override2" then geOverride2 gen else geOverride1 gen)
  (geKeep gen) (geArrow gen) (geAssign gen) (geAt gen)

-- | The bundle, looked up by name (for the satellite 'Deriver1'\/'Deriver2's).
lookupOvTcs :: String -> TcPluginM OvTcs
lookupOvTcs wrap = OvTcs
  <$> lookupTyConMaybe "Stock.Override" wrap
  <*> lookupTyConMaybe "Stock.Override" "Keep"
  <*> lookupTyConMaybe "Stock.Override" "-->"
  <*> lookupTyConMaybe "Stock.Override" ":="
  <*> lookupTyConMaybe "Stock.Override" "At"

-- | As 'peelOverride1', but taking the 'TyCon' bundle directly so callers
-- without a 'GenEnv' (the companion 'Deriver1's) can peel @Override1@ too.
peelOverride1With :: OvTcs -> Type -> (Type, Maybe [Type])
peelOverride1With tcs f = case ovWrap tcs of
  Just ov1Tc | Just (tc, [_, _, realF, cfg]) <- splitTyConApp_maybe f, tc == ov1Tc
             -> (realF, decodeOvCfg tcs realF cfg)
  _          -> (f, Nothing)

-- | Decode an @Override1@\/@Override2@ config to the (first) constructor's
-- per-field /raw/ modifiers (@Keep@ where a field is unaddressed).  Both the
-- positional @'[ '[m, _, …] ]@ form AND the field-keyed entry list @'[ "x" ':=
-- m, 'C '--> 0 '--> m, … ]@ work — the same surface as value @Override@, only
-- the modifier kind differs (a functor here).  'modifierType' is /not/ applied:
-- the synthesizers receive @m@ and reshape @h a@ to @m a@ themselves.
decodeOvCfg :: OvTcs -> Type -> Type -> Maybe [Type]
decodeOvCfg tcs realInner cfg =
  case decodePositional cfg of
    Just perCon -> listToMaybe perCon                -- positional [[..]] form
    Nothing -> do                                    -- field-keyed entry list
      arrowTc <- ovArrow tcs ; assignTc <- ovAssign tcs
      atTc    <- ovAt tcs    ; keepTc   <- ovKeep tcs
      fTc     <- tyConAppTyCon_maybe realInner
      let dcons = tyConDataCons fTc
      guard (not (null dcons))
      entries <- promotedListElems cfg >>= traverse (decodeEntry arrowTc assignTc atTc)
      cells   <- either (const Nothing) Just (resolveCellsRaw dcons realInner entries)
      -- @realInner@ is an unsaturated @j -> Type@ here, so use the source arity
      -- (not 'fieldTysAt', which would instantiate the datacon and panic).
      Just [ fromMaybe (mkTyConTy keepTc) (lookup (0, fi) cells)
           | fi <- [0 .. dataConSourceArity (head dcons) - 1] ]

-- | The modifier functor for field @i@ under an @Override1@ config, if any (and
-- not @Keep@): the field's @h a@ is then reshaped to @m a@.
override1Mod :: GenEnv -> Maybe [Type] -> Int -> Maybe Type
override1Mod gen = override1ModWith (geKeep gen)

-- | As 'override1Mod', but taking the @Keep@ 'TyCon' directly (for 'Deriver1's).
override1ModWith :: Maybe TyCon -> Maybe [Type] -> Int -> Maybe Type
override1ModWith mKeep mMods i = case mMods of
  Just mods | i < length mods
            , let m = fixMod1Kind (mods !! i)
            , not (maybe False (\k -> tyConAppTyCon_maybe m == Just k) mKeep)
            -> Just m
  _ -> Nothing

-- | An @Override1@ modifier must have kind @Type -> Type@.  A /poly-kinded/
-- modifier such as @Const Int@ (kind @forall {k}. k -> Type@) decoded from the
-- sparse @Con at i via M@ surface keeps an un-instantiated kind variable as its
-- second argument, so @Functor (Const Int)@ would be requested at a skolem kind
-- and find no instance.  When the kind is not already @Type -> Type@, default
-- the modifier's free @Type@-kinded variables to @Type@ — this fixes the leftover
-- kind argument while leaving genuine functor variables (kind @Type -> Type@, as
-- in a polymorphic @Compose f g@) untouched.
fixMod1Kind :: Type -> Type
fixMod1Kind m0
  | typeKind m0 `eqType` mkVisFunTyMany liftedTypeKind liftedTypeKind = m0
  | otherwise = substTyWith kvs (map (const liftedTypeKind) kvs) m0
  where kvs = filter ((`eqType` liftedTypeKind) . tyVarKind)
                     (nonDetEltsUniqSet (tyCoVarsOfType m0))

-- | The @Stock2@\/@Override2@ analogue of 'fixMod1Kind': a modifier must have
-- kind @k -> k -> Type@ (where @k@ is the arrow's object kind).  A modifier
-- decoded from the sparse @Con at i := M@ surface can carry skolem /kind/
-- variables for phantom parameters (e.g. @Basic m a b@'s @a@\/@b@); default those
-- (the free @Type@-kinded variables) to @k@ when the kind is not already @k -> k
-- -> Type@, leaving genuine value variables (a polymorphic @Op cat@, kind @k -> k
-- -> Type@) untouched.  Replaces the older "default /all/ free vars" pass, which
-- wrongly clobbered such value variables.
fixMod2Kind :: Kind -> Type -> Type
fixMod2Kind kTy m0
  | typeKind m0 `eqType` mkVisFunTyMany kTy (mkVisFunTyMany kTy liftedTypeKind) = m0
  | otherwise = substTyWith kvs (map (const kTy) kvs) m0
  where kvs = filter ((`eqType` liftedTypeKind) . tyVarKind)
                     (nonDetEltsUniqSet (tyCoVarsOfType m0))

-- | @Stock1 (Override1 cfg realF) t ~R realF t@ — two newtype hops (one when
-- there is no @Override1@ wrapper).
coDown1 :: GenEnv -> TyCon -> Type -> Type -> Type -> Type -> Coercion
coDown1 gen = coDown1With (geOverride1 gen)

-- | As 'coDown1', but taking the @Override1@ 'TyCon' directly (for 'Deriver1's).
coDown1With :: Maybe TyCon -> TyCon -> Type -> Type -> Type -> Type -> Coercion
coDown1With mOv1 st1Tc wrappedTy f0 realF t = mkTransCo
  (mkUnbranchedAxInstCo Representational (newTyConCo st1Tc) (tyConAppArgs wrappedTy ++ [t]) [])
  (case mOv1 of
     Just ov1Tc | tyConAppTyCon_maybe f0 == Just ov1Tc ->
       mkUnbranchedAxInstCo Representational (newTyConCo ov1Tc) (tyConAppArgs f0 ++ [t]) []
     _ -> mkRepReflCo (mkAppTy realF t))

-- | The @Stock2@ counterpart of 'peelOverride1With': peel @Override2 cfg realP@
-- to the real constructor and its per-field positional modifiers (for 'Deriver2's).
peelOverride2With :: OvTcs -> Type -> (Type, Maybe [Type])
peelOverride2With tcs p = case ovWrap tcs of
  Just ov2Tc | Just (tc, [_, rp, cfg]) <- splitTyConApp_maybe p, tc == ov2Tc
             -> (rp, decodeOvCfg tcs rp cfg)
  _          -> (p, Nothing)

-- | @Stock2 (Override2 cfg realP) t1 t2 ~R realP t1 t2@ — two newtype hops (one
-- when there is no @Override2@ wrapper).  For 'Deriver2's.
coDown2With :: Maybe TyCon -> TyCon -> Type -> Type -> Type -> Type -> Type -> Coercion
coDown2With mOv2 st2Tc wrappedTy p0 realP t1 t2 = mkTransCo
  (mkUnbranchedAxInstCo Representational (newTyConCo st2Tc) (tyConAppArgs wrappedTy ++ [t1, t2]) [])
  (case mOv2 of
     Just ov2Tc | tyConAppTyCon_maybe p0 == Just ov2Tc ->
       mkUnbranchedAxInstCo Representational (newTyConCo ov2Tc) (tyConAppArgs p0 ++ [t1, t2]) []
     _ -> mkRepReflCo (mkAppTy (mkAppTy realP t1) t2))

-- | Recognise @Stock (Override T cfg)@ and build the override representation of
-- @T@.  The unwrap coercion chains through /both/ newtypes; fields named in
-- @cfg@ take their modifier type, with a per-cell @realτ ~R modτ@ coercion
-- emitted as a wanted (so GHC validates the override and reports a clean error
-- if it isn't coercible); unnamed fields are unchanged.  'Nothing' if this is
-- not an @Override@; @Left@ if it is but malformed.  v1: single-constructor,
-- keyed by record-field name, modifiers saturated (@Type@, pin) or unary
-- (@Type -> Type@, broadcast).
-- | Representational primitive equality @a ~R# b@ — the wanted whose evidence
-- coercion we splice per overridden cell.  (Renamed in GHC 9.14.)
mkStockReprEq :: Type -> Type -> Type
#if MIN_VERSION_ghc(9,14,0)
mkStockReprEq = mkReprEqPred
#else
mkStockReprEq = mkReprPrimEqPred
#endif

-- | Pure decode of @Stock (Override T cfg)@ to @T@ and its constructors paired
-- with their per-field /modifier/ types (@Keep@ or an unmatched cell ⇒ the real
-- field type).  The 'Generic' Rep rewriter ('Stock.Generic.rewriteRep') needs
-- only these types; the value-level coercion wanteds are emitted by the solver
-- ('synthGeneric' via 'mkOverrideRepr'), and both compute identical modifier
-- types (same 'modifierType') so the @Rep@ and @from@\/@to@ cohere.  'Nothing'
-- if @arg@ is not a @Stock (Override …)@ (the caller falls back to 'mkRepr').
overrideFieldTypes :: GenEnv -> Type -> Maybe (Type, [(DataCon, [Type])])
overrideFieldTypes gen arg = do
  ourStock <- geStock gen
  overTc   <- geOverride gen
  keepTc   <- geKeep gen ; arrowTc <- geArrow gen
  assignTc <- geAssign gen ; atTc <- geAt gen
  (stockTc, [innerOver]) <- splitTyConApp_maybe arg
  guard (stockTc == ourStock)
  (oTc, oArgs) <- splitTyConApp_maybe innerOver
  guard (oTc == overTc)
  (cfg : realInner : _) <- pure (reverse oArgs)
  innerTc <- tyConAppTyCon_maybe realInner
  let dcons = tyConDataCons innerTc
  guard (not (null dcons))
  perCon <-
    case decodePositional cfg of
      Just perCon                           -- positional [[..]] form
        | length perCon == length dcons ->
            sequence (zipWith (posCon keepTc realInner) dcons perCon)
        | otherwise -> Nothing
      Nothing -> do                          -- entry-list / --> path form
        entries <- promotedListElems cfg >>= traverse (decodeEntry arrowTc assignTc atTc)
        case resolveCells dcons realInner entries of
          Left _      -> Nothing
          Right cells -> Just [ [ fromMaybe rft (lookup (ci, fi) cells)
                                | (fi, rft) <- zip [0 ..] (fieldTysAt realInner dc) ]
                              | (ci, dc) <- zip [0 :: Int ..] dcons ]
  pure (realInner, zip dcons perCon)
  where
    -- one positional constructor: each slot a modifier type or @Keep@ (no change)
    posCon keepTc realInner dc mods
      | length mods /= length rfts = Nothing
      | otherwise = sequence (zipWith cell rfts mods)
      where rfts = fieldTysAt realInner dc
            cell rft m
              | tyConAppTyCon_maybe m == Just keepTc = Just rft
              | otherwise = either (const Nothing) Just (modifierType m rft)

mkOverrideRepr :: GenEnv -> CtLoc -> Type -> TcPluginM (Maybe (Either SDoc (Repr, [Ct])))
mkOverrideRepr gen loc wrappedTy
  | Just ourStock <- geStock gen
  , Just overTc   <- geOverride gen
  , Just assignTc <- geAssign gen
  , Just (stockTc, [innerOver]) <- splitTyConApp_maybe wrappedTy
  , stockTc == ourStock
  , Just (oTc, oArgs) <- splitTyConApp_maybe innerOver
  , oTc == overTc
  , (cfg : realInner : _) <- reverse oArgs  -- last two visible args (drop the invisible cfg kind)
  , Just atTc    <- geAt gen
  , Just keepTc  <- geKeep gen
  , Just arrowTc <- geArrow gen
  = Just <$> buildOverride loc ourStock overTc assignTc atTc keepTc arrowTc innerOver cfg realInner
  | otherwise = pure Nothing

-- | The body of 'mkOverrideRepr', once it is known to be an @Override@.
-- Two config shapes (see @docs\/override-design.md@): a /positional/
-- list-of-lists @'[ '[m, …], … ]@ (one inner list per constructor, one element
-- per field, @Keep@ = no change), or an /entry list/ @'[ sel ':= m, 'C --> n
-- --> m, … ]@ — both multi-constructor, selector- and path-addressed.
buildOverride :: CtLoc -> TyCon -> TyCon -> TyCon -> TyCon -> TyCon -> TyCon
              -> Type -> Type -> Type -> TcPluginM (Either SDoc (Repr, [Ct]))
buildOverride loc ourStock overTc assignTc atTc keepTc arrowTc innerOver cfg realInner =
  case tyConAppTyCon_maybe realInner of
    Nothing -> bad (text "Override target is not a concrete algebraic type:" <+> ppr realInner)
    Just innerTc -> case tyConDataCons innerTc of
      [] -> bad (text "Override: type has no constructors:" <+> ppr realInner)
      dcons
        | any dcUnpacked dcons -> bad (text "Override: a constructor has UNPACKed/strict-unboxed"
                                       <+> text "or existential fields, unsupported")
        -- positional [[..]] form: one inner list per constructor
        | Just perCon <- decodePositional cfg ->
            buildPositional loc ourStock overTc keepTc innerOver cfg realInner dcons perCon
        -- entry-list form ( := / At / --> paths ), multi-constructor
        | otherwise ->
            case promotedListElems cfg >>= traverse (decodeEntry arrowTc assignTc atTc) of
              Nothing      -> bad (text "Override config is not a concrete list of"
                                   <+> text "selector := modifier / path --> modifier entries:" <+> ppr cfg)
              Just entries -> resolveOverride loc ourStock overTc innerOver cfg realInner dcons entries
  where bad = pure . Left

-- | A positional config @'[ '[m00, m01, …], … ]@ as per-constructor,
-- per-field modifier lists, or 'Nothing' if @cfg@ is not a concrete
-- list-of-lists (in which case the entry-list decoder is tried instead).
decodePositional :: Type -> Maybe [[Type]]
decodePositional cfg = case promotedListElems cfg of
  Just es@(_ : _) -> traverse promotedListElems es   -- one inner list per constructor
  _               -> Nothing                          -- empty @'[]@ is identity, not "0
                                                      -- constructors": fall through to the
                                                      -- entry-list branch (@resolveOverride []@)

-- | Build the 'Repr' for a positional config: each constructor's inner list
-- gives a modifier per field — @Keep@ leaves the field, any other type @m@
-- replaces it (kind-dispatched 'pin' vs 'broadcast' by 'modifierType'), with a
-- per-cell @realτ ~R modτ@ coercion emitted as a wanted.
buildPositional :: CtLoc -> TyCon -> TyCon -> TyCon -> Type -> Type -> Type
                -> [DataCon] -> [[Type]] -> TcPluginM (Either SDoc (Repr, [Ct]))
buildPositional loc ourStock overTc keepTc innerOver cfg realInner dcons perCon
  | length perCon /= length dcons =
      pure (Left (text "Override: positional config has" <+> int (length perCon)
                  <+> text "constructor list(s) but" <+> ppr realInner <+> text "has"
                  <+> int (length dcons)))
  | otherwise = do
      let co = mkTransCo (mkUnbranchedAxInstCo Representational (newTyConCo ourStock) [innerOver] [])
                         (mkUnbranchedAxInstCo Representational (newTyConCo overTc) [typeKind cfg, realInner, cfg] [])
      results <- traverse (uncurry conInfo) (zip dcons perCon)
      pure $ case sequence results of
        Left err   -> Left err
        Right cws  -> Right (Repr realInner co (map fst cws), concatMap snd cws)
  where
    conInfo :: DataCon -> [Type] -> TcPluginM (Either SDoc (ConInfo, [Ct]))
    conInfo dc mods
      | length mods /= length realFts =
          pure (Left (text "Override: constructor" <+> ppr dc <+> text "has" <+> int (length realFts)
                      <+> text "field(s) but its positional list has" <+> int (length mods)))
      | otherwise = do
          cells <- traverse cell (zip realFts mods)
          pure $ case sequence cells of
            Left err -> Left err
            Right fs -> Right (ConInfo dc (map (fst . fst) fs) (map (snd . fst) fs)
                              , concatMap snd fs)
      where realFts = fieldTysAt realInner dc
    -- one field: Keep ⇒ (realτ, Refl); modifier m ⇒ (modτ, evidence coercion + wanted)
    cell :: (Type, Type) -> TcPluginM (Either SDoc ((Type, Coercion), [Ct]))
    cell (ft, m)
      | tyConAppTyCon_maybe m == Just keepTc = pure (Right ((ft, mkRepReflCo ft), []))
      | otherwise = case modifierType m ft of
          Left err    -> pure (Left err)
          Right modTy -> do
            ev <- newWanted loc (mkStockReprEq ft modTy)
            pure (Right ((modTy, ctEvCoercion ev), [mkNonCanonical ev]))

-- | A path hop (design §4): a constructor, a field by position, or a field by
-- label.  Constructor hops match by /occ-name/, so both @'P@ and (for a
-- single-constructor type) the bare type name resolve.
data Hop = HopCon FastString | HopPos Integer | HopLabel FastString

-- | A decoded entry's address: a @-->@ \/ @:=@ path of hops (narrowing the
-- @(constructor, field)@ scope), or a type selector.
data Addr = AddrPath [Hop] | AddrType Type

-- | Resolve decoded @(addr, modifier)@ entries against /all/ the type's
-- constructors: turn each address into its cell set @(ctorIndex, fieldIndex)@,
-- reject any cell claimed twice, kind-dispatch each modifier per cell, emit the
-- per-cell coercion wanteds, and assemble the (multi-constructor) 'Repr'.
resolveOverride :: CtLoc -> TyCon -> TyCon -> Type -> Type -> Type -> [DataCon]
                -> [(Addr, Type)] -> TcPluginM (Either SDoc (Repr, [Ct]))
resolveOverride loc ourStock overTc innerOver cfg realInner dcons entries =
  case resolveCells dcons realInner entries of
    Left err    -> pure (Left err)
    Right cells -> do
      tagged <- for cells \((ci, fi), modTy) -> do
        let realFt = fieldTysAt realInner (dcons !! ci) !! fi
        ev <- newWanted loc (mkStockReprEq realFt modTy)
        pure (((ci, fi), (modTy, ctEvCoercion ev)), mkNonCanonical ev)
      let cellMap = map fst tagged
          wanteds = map snd tagged
          -- Stock (Override T cfg) ~R Override T cfg ~R T
          co = mkTransCo (mkUnbranchedAxInstCo Representational (newTyConCo ourStock) [innerOver] [])
                         (mkUnbranchedAxInstCo Representational (newTyConCo overTc) [typeKind cfg, realInner, cfg] [])
          cons = [ ConInfo dc (map fst fields) (map snd fields)
                 | (ci, dc) <- zip [0 :: Int ..] dcons
                 , let fields = [ fromMaybe (ft, mkRepReflCo ft) (lookup (ci, fi) cellMap)
                                | (fi, ft) <- zip [0 :: Int ..] (fieldTysAt realInner dc) ] ]
      pure (Right (Repr realInner co cons, wanteds))

-- | As 'resolveCells', but keeping the /raw/ modifier @m@ per cell (not
-- 'modifierType'-applied) — for @Override1@\/@Override2@, whose synthesizers
-- want the bare functor modifier (they reshape @h a@ to @m a@ themselves).
resolveCellsRaw :: [DataCon] -> Type -> [(Addr, Type)] -> Either SDoc [((Int, Int), Type)]
resolveCellsRaw dcons targetTy = go []
  where
    go _       []                 = Right []
    go claimed ((addr, m) : rest) = do
      cells <- resolveAddr dcons targetTy addr
      case filter (`elem` claimed) cells of
        clash@(_ : _) -> Left (text "Override: cell(s)" <+> ppr clash
                               <+> text "claimed by more than one entry (make them disjoint)")
        [] -> ((map (\c -> (c, m)) cells) ++) <$> go (cells ++ claimed) rest

-- | Resolve every entry to its cells (with kind-dispatched modifier types),
-- left to right, enforcing the no-overlap law against the cells already claimed.
resolveCells :: [DataCon] -> Type -> [(Addr, Type)]
             -> Either SDoc [((Int, Int), Type)]
resolveCells dcons targetTy = go []
  where
    go _       []                 = Right []
    go claimed ((addr, m) : rest) = do
      cells <- resolveAddr dcons targetTy addr
      case filter (`elem` claimed) cells of
        clash@(_ : _) -> Left (text "Override: cell(s)" <+> ppr clash
                               <+> text "claimed by more than one entry (make them disjoint)")
        [] -> do
          here <- for cells \(ci, fi) ->
                    (,) (ci, fi) <$> modifierType m (fieldTysAt targetTy (dcons !! ci) !! fi)
          (here ++) <$> go (cells ++ claimed) rest

-- | Resolve one address to its @(ctorIndex, fieldIndex)@ cell set.
resolveAddr :: [DataCon] -> Type -> Addr -> Either SDoc [(Int, Int)]
resolveAddr dcons targetTy addr = case addr of
  AddrType t
    | t `eqType` targetTy -> Right (allCells dcons targetTy)
    | otherwise -> case [ (ci, fi) | (ci, dc) <- zip [0 ..] dcons
                                   , (fi, ft) <- zip [0 ..] (fieldTysAt targetTy dc)
                                   , ft `eqType` t ] of
        [] -> Left (text "Override: no field of type" <+> quotes (ppr t))
        cs -> Right cs
  AddrPath hops -> foldHops dcons targetTy (allCells dcons targetTy) hops

-- | Narrow the cell scope by each hop in turn.
foldHops :: [DataCon] -> Type -> [(Int, Int)] -> [Hop] -> Either SDoc [(Int, Int)]
foldHops _     _        scope []               = Right scope
foldHops dcons targetTy scope (HopCon nm : hs) =
  case [ ci | (ci, dc) <- zip [0 ..] dcons, occNameFS (getOccName dc) == nm ] of
    []  -> Left (text "Override: unknown constructor" <+> quotes (ftext nm))
    cis -> foldHops dcons targetTy (filter ((`elem` cis) . fst) scope) hs
foldHops dcons targetTy scope (HopPos n : hs) =
  case filter ((== fromInteger n) . snd) scope of
    []  -> Left (text "Override: no field at position" <+> integer n <+> text "in the addressed scope")
    sc' -> foldHops dcons targetTy sc' hs
foldHops dcons targetTy scope (HopLabel l : hs) =
  case [ (ci, fi) | (ci, fi) <- scope, labelAt (dcons !! ci) fi == Just (unpackFS l) ] of
    []  -> Left (text "Override: no field labelled" <+> quotes (ftext l) <+> text "in the addressed scope")
    sc' -> foldHops dcons targetTy sc' hs

-- | Every @(ctorIndex, fieldIndex)@ cell of the type.  Uses the source arity
-- (not 'fieldTysAt') so it is safe when @targetTy@ is an unsaturated @j -> Type@
-- (the @Override1@\/@Override2@ case).
allCells :: [DataCon] -> Type -> [(Int, Int)]
allCells dcons _ =
  [ (ci, fi) | (ci, dc) <- zip [0 ..] dcons, fi <- [0 .. dataConSourceArity dc - 1] ]

-- | The record label of a constructor's @i@-th field, if it has one.
labelAt :: DataCon -> Int -> Maybe String
labelAt dc i =
  let ls = map (occNameString . nameOccName . flSelector) (dataConFieldLabels dc)
  in if i < length ls then Just (ls !! i) else Nothing

-- | Kind-dispatch a modifier: a saturated @Type@ pins the field to that type;
-- a unary @Type -> Type@ is applied to the field's own type (broadcast).
modifierType :: Type -> Type -> Either SDoc Type
modifierType m fieldTy
  | k `eqType` liftedTypeKind                              = Right m
  | k `eqType` mkVisFunTyMany liftedTypeKind liftedTypeKind = Right (mkAppTy m fieldTy)
  | otherwise = Left (text "Override: modifier" <+> ppr m <+> text "has unsupported kind"
                      <+> ppr k <+> text "(expected Type or Type -> Type)")
  where k = typeKind m

-- | A balanced list of the elements of a promoted type-level list
-- (@'[a, b, …]@), or 'Nothing' if @ty@ is not a concrete promoted list.
promotedListElems :: Type -> Maybe [Type]
promotedListElems ty = do
  (tc, args) <- splitTyConApp_maybe ty
  if | tc == promotedNilDataCon  -> Just []
     | tc == promotedConsDataCon -> case args of
         [_k, x, rest] -> (x :) <$> promotedListElems rest
         _             -> Nothing
     | otherwise -> Nothing

-- | Decode one config entry into its address and modifier.  Three surfaces:
-- a @-->@ path (@'P --> 0 --> m@), a @:=@ entry (@"x" := m@ or @At C n := m@),
-- or — still through @:=@ — a type selector (@Int := m@).  Robust to leading
-- invisible kind arguments (the visible operands are the last two).
decodeEntry :: TyCon -> TyCon -> TyCon -> Type -> Maybe (Addr, Type)
decodeEntry arrowTc assignTc atTc e
  | Just (hops, m) <- decodeArrow arrowTc e =
      (\hs -> (AddrPath hs, m)) <$> traverse decodeHop hops
  | Just (tc, args) <- splitTyConApp_maybe e, tc == assignTc
  , (m : sel : _) <- reverse args = (, m) <$> decodeSel atTc sel
  | otherwise = Nothing

-- | Flatten a right-nested @a --> b --> … --> m@ into its hop types and the
-- terminal modifier; 'Nothing' if @e@ is not a @-->@ application.
decodeArrow :: TyCon -> Type -> Maybe ([Type], Type)
decodeArrow arrowTc e = do
  (tc, args) <- splitTyConApp_maybe e
  guard (tc == arrowTc)
  case reverse args of
    (rhs : lhs : _) -> case decodeArrow arrowTc rhs of
      Just (hs, m) -> Just (lhs : hs, m)   -- rhs continues the path
      Nothing      -> Just ([lhs], rhs)    -- rhs is the terminal modifier
    _ -> Nothing

-- | Classify a path hop by kind: 'Symbol' ⇒ label, 'Nat' ⇒ position, otherwise
-- a (promoted constructor \/ type) matched later by occ-name.
decodeHop :: Type -> Maybe Hop
decodeHop h
  | Just fs <- isStrLitTy h          = Just (HopLabel fs)
  | Just n  <- isNumLitTy h          = Just (HopPos n)
  | Just tc <- tyConAppTyCon_maybe h = Just (HopCon (occNameFS (getOccName tc)))
  | otherwise                        = Nothing

-- | Classify the left of @:=@: a 'Symbol' is a label path, @At C n@ a
-- constructor+position path, anything else a type selector.
decodeSel :: TyCon -> Type -> Maybe Addr
decodeSel atTc sel
  | Just fs <- isStrLitTy sel = Just (AddrPath [HopLabel fs])
  | Just (tc, args) <- splitTyConApp_maybe sel, tc == atTc
  , (pos : con : _) <- reverse args, Just n <- isNumLitTy pos
  , Just ctc <- tyConAppTyCon_maybe con =
      Just (AddrPath [HopCon (occNameFS (getOccName ctc)), HopPos n])
  | otherwise = Just (AddrType sel)

-- | Does any cell carry a non-trivial override (a modifier coercion that isn't
-- reflexivity)?  The raw @viaSynth@ synthesizers (Ord\/Show\/Read\/Enum\/Ix)
-- recompute field types from the constructor and so cannot honour an override;
-- the dispatcher uses this to reject them loudly rather than silently ignore it.
reprOverridden :: Repr -> Bool
reprOverridden = any (any (not . isReflCo) . ciFieldCos) . rCons

-- Representation predicates ("checking the datatype representation").
reprHasFields, reprIsEnum, reprSingleCon, reprEmpty :: Repr -> Bool
reprHasFields = any (not . null . ciFields) . rCons
-- GHC: an enumeration has >= 1 nullary constructor.  Requiring non-empty here
-- makes Enum/Ix/Bounded reject 0-constructor types cleanly (rather than build
-- degenerate Core: maxTag = -1, head/last of []), matching GHC's rejection.
reprIsEnum    r = not (reprEmpty r) && not (reprHasFields r)
reprSingleCon = (== 1) . length . rCons
reprEmpty     = null . rCons

-- | Does any constructor have fields whose runtime representation differs from
-- their source types?  This happens with @UNPACK@ / @-funbox-small-strict-fields@
-- (a strict @!Int@ becomes @Int#@) and with existentials/GADTs.  We match on the
-- source types, so such constructors would yield ill-typed Core — we refuse them.
reprUnpacked :: Repr -> Bool
reprUnpacked = any (dcUnpacked . ciCon) . rCons

-- | True if a constructor's runtime arg representation differs from its source
-- arg types (UNPACK, @-funbox-small-strict-fields@, existentials, …).
dcUnpacked :: DataCon -> Bool
dcUnpacked dc =
  let rep  = map scaledThing (dataConRepArgTys dc)
      orig = map scaledThing (dataConOrigArgTys dc)
  in length rep /= length orig || not (and (zipWith eqType rep orig))

-- | Does any constructor have a field whose type is headed by a /family/
-- instance (a @data@\/@type@ family — e.g. @cardano-crypto@'s @VerificationKey
-- HydraKey@)?  A pattern variable bound at such a field's representation tycon
-- makes Core codegen panic (@StgToCmm: variable not found@), so we refuse it
-- cleanly instead.  Same root as 'dcUnpacked' (representation ≠ source type).
reprFamilyField :: Repr -> Bool
reprFamilyField = any (dcFamilyField . ciCon) . rCons

dcFamilyField :: DataCon -> Bool
dcFamilyField =
  any (maybe False isFamilyTyCon . tyConAppTyCon_maybe) . map scaledThing . dataConOrigArgTys

-- | Apply a class's dictionary constructor: @C:Cls \@ty m1 .. mn@.
mkClassDict :: Class -> Type -> [CoreExpr] -> CoreExpr
mkClassDict cls ty methods =
  mkApps (Var (dataConWorkId (classDataCon cls))) (Type ty : methods)

-- | A constructor's field types, instantiated at the inner type's arguments,
-- so a parameterised type such as @Pair Int@ yields @[Int, Int]@ rather than
-- @[a, a]@ (and @Pair a@ yields the skolem @[a, a]@).
fieldTysAt :: Type -> DataCon -> [Type]
fieldTysAt innerTy dc = map scaledThing (dataConInstOrigArgTys dc (tyConAppArgs innerTy))

-- | Apply a constructor, supplying the inner type's type arguments first
-- (e.g. @Pair \@Int e1 e2@), so it works for parameterised types.
conAppAt :: Type -> DataCon -> [CoreExpr] -> CoreExpr
conAppAt innerTy dc args = mkCoreConApps dc (map Type (tyConAppArgs innerTy) ++ args)

-- | Build a (possibly self-referential) dictionary: @let rec d = C:Cls ty (mk d)
-- in d@.  The callback receives the dictionary binder so fields can refer back
-- to it (e.g. to use class default methods).
recClassDict :: Class -> Type -> (Id -> TcPluginM [CoreExpr]) -> TcPluginM CoreExpr
recClassDict cls ty mk = do
  dvar   <- freshId (mkClassPred cls [ty]) "dict"
  fields <- mk dvar
  pure (Let (Rec [(dvar, mkClassDict cls ty fields)]) (Var dvar))

-- | Build a recursive dictionary giving explicit superclass dicts and explicit
-- implementations for the listed method indices; every other method comes from
-- the class's own default method (applied to the recursive dictionary).  This
-- is how we fill many-method classes (@Foldable@) from a single key method.
recDictWith :: Class -> Type -> [CoreExpr] -> [(Int, CoreExpr)] -> TcPluginM CoreExpr
recDictWith cls ty supers overrides = do
  dvar <- freshId (mkClassPred cls [ty]) "dict"
  methodFields <- for (zip [0 ..] (classMethods cls)) \(i, _) ->
    case lookup i overrides of
      Just e  -> pure e
      Nothing -> do dm <- defMethId cls i
                    pure (mkApps (Var dm) [Type ty, Var dvar])
  pure (Let (Rec [(dvar, mkClassDict cls ty (supers ++ methodFields))]) (Var dvar))

-- | How a constructor field relates to the functor parameter @a@.
data FieldKind = FParam | FConst | FApp Type   -- ^ is @a@ / no @a@ / @H a@ (covariant)

classifyField :: TyVar -> Type -> Type -> Maybe FieldKind
classifyField atv aTy ft
  | ft `eqType` aTy                              = Just FParam
  | not (atv `elemVarSet` tyCoVarsOfType ft)     = Just FConst
  | Just (h, larg) <- splitAppTy_maybe ft
  , larg `eqType` aTy
  , not (atv `elemVarSet` tyCoVarsOfType h)      = Just (FApp h)
  | otherwise                                    = Nothing

-- | How to use one constructor field, by its relationship to the parameter.
-- This is the single place that distinguishes a lifted class (@Eq1@\/@Ord1@\/
-- @Show1@\/@Read1@) from its twin: the @onParam@ leaf is what changes (the
-- supplied function vs the field's own instance).  @onConst@\/@onApply@ receive
-- the wanted-evidence the field needs.
-- | A field walk for the lifted classes (@Eq1@\/@Ord1@\/@Show1@\/@Read1@).  The
-- per-field operation @op@ is built by folding 'wLift' over the field's functor
-- /layers/, starting from 'wLeaf' at the parameter @a@; 'wApply' then applies the
-- finished operation to the field value(s).  This is the lifted analogue of GHC's
-- @functorLikeTraverse@, so a nested field @[[a]]@ becomes @liftEq (liftEq f)@.
-- @op@ is class-specific (a comparator for @Eq1@\/@Ord1@; an @(sp, sl)@\/@(rp,
-- rl)@ method pair for @Show1@\/@Read1@); @r@ is the per-field result.
data Walk op r = Walk
  { wLeaf  :: op                                       -- ^ the operation at @a@
  , wLift  :: CtEvidence -> Type -> Type -> op -> op
    -- ^ lift @op@ over one functor layer: the lifted-class evidence for the layer
    -- functor @h@, the functor @h@, the element type (parameter still the field's
    -- @atv@), and the inner operation.
  , wConst :: CtEvidence -> Type -> r                  -- ^ a wholly-constant field
  , wApply :: op -> Type -> (Type -> Coercion) -> r
    -- ^ apply the finished @op@: it operates on the given type (parameter @atv@),
    -- with a coercion @field[t] ~R opType[t]@ ('Refl' unless an @Override1@
    -- reshaped the field).
  }

-- | Build a field's lifted operation by walking its functor layers, emitting the
-- wanted each layer needs (the lifted @C1 h@ per layer, or @C h@ for a wholly
-- constant field).  Under an @Override1@ the /whole/ field is reshaped to @m a@
-- (one level, like @Functor@\/@Foldable@), and the reshape is validated at the
-- closed type @()@ so an unsound override is rejected.  Without an override a
-- nested field @h (g (… a))@ folds the lift over each layer.  'Nothing' if the
-- field shape is unsupported (contravariant, a tuple mentioning @a@, …).
interpField :: Class       -- ^ the constant-field class (@Eq@\/@Ord@\/@Show@\/@Read@)
            -> Class       -- ^ the lifted class      (@Eq1@\/@Ord1@\/@Show1@\/@Read1@)
            -> TyVar -> Type -> CtLoc
            -> Maybe Type  -- ^ @Override1@ modifier for this field, if any
            -> Walk op r -> Type -> TcPluginM (Maybe (r, [Ct]))
interpField constCls liftCls atv aTy loc mMod w ftA = case mMod of
  Just m -> do
    ev <- newWanted loc (mkClassPred liftCls [m])
    vw <- newWanted loc (mkStockReprEq (substTyWith [atv] [unitTy] ftA) (mkAppTy m unitTy))
    let coB t = mkStockCo (PluginProv "stock") Representational
                  (substTyWith [atv] [t] ftA) (mkAppTy m t)
    pure (Just ( wApply w (wLift w ev m aTy (wLeaf w)) (mkAppTy m aTy) coB
               , [mkNonCanonical ev, mkNonCanonical vw] ))
  Nothing
    | not (atv `elemVarSet` tyCoVarsOfType ftA) -> do
        ev <- newWanted loc (mkClassPred constCls [ftA])
        pure (Just (wConst w ev ftA, [mkNonCanonical ev]))
    | otherwise -> do
        mr <- buildNest ftA
        pure (fmap (\(op, ws) -> (wApply w op ftA reflB, ws)) mr)
  where
    reflB t = mkRepReflCo (substTyWith [atv] [t] ftA)
    -- the operation for an element type @t@ (parameter still @atv@): 'wLeaf' at
    -- @a@, else lift the inner operation over the head functor @h@.
    buildNest t
      | t `eqType` aTy = pure (Just (wLeaf w, []))
      | Just (h, larg) <- splitAppTy_maybe t
      , not (atv `elemVarSet` tyCoVarsOfType h) = do
          mi <- buildNest larg
          case mi of
            Nothing         -> pure Nothing
            Just (iop, iws) -> do
              ev <- newWanted loc (mkClassPred liftCls [h])
              pure (Just (wLift w ev h larg iop, mkNonCanonical ev : iws))
      | otherwise = pure Nothing

-- | The field types of a constructor with the @Stock1@ parameter set to @ty@.
fieldsAt :: [Type] -> DataCon -> Type -> [Type]
fieldsAt fixed dc ty = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [ty]))

-- | The two-scrutinee SOP walk — the @Stock1@ counterpart to 'matchSOP'
-- (which is single-scrutinee, in "Stock.Derive").  Walk two values of the same
-- @Stock1 F@ shape in lock-step: matching constructors combine their per-field
-- results, mismatched constructors give a fixed answer.  This is the skeleton
-- shared by @liftEq@ (combine = short-circuit @&&@, mismatch = @False@) and
-- @liftCompare@ (combine = lexicographic, mismatch = tag order).  @fieldOp@
-- produces one field-pair's result (via 'interpField'); @combine@ folds a
-- constructor's field results.
zipLift2 :: TyCon -> [Type] -> (Type -> Coercion)
         -> Type -> Type -> Type             -- a, b, result type
         -> Id -> Id                         -- the two scrutinees (fa, fb)
         -> (Int -> Int -> CoreExpr)         -- mismatched-constructor result
         -> ([CoreExpr] -> TcPluginM CoreExpr)            -- combine field results
         -> (Int -> Type -> Id -> Id -> TcPluginM (Maybe (CoreExpr, [Ct])))  -- per field pair (with index)
         -> TcPluginM (Maybe (CoreExpr, [Ct]))
zipLift2 fTc fixed coAt aTy bTy resTy faId fbId mismatch combine fieldOp = do
  let dcons   = tyConDataCons fTc
      innerA  = mkTyConApp fTc (fixed ++ [aTy])
      innerB  = mkTyConApp fTc (fixed ++ [bTy])
      indexed = zip [0 :: Int ..] dcons
      freshFields dc ty = zipWithM (\n ft -> freshId ft ("x" ++ show n)) [0 :: Int ..]
                                   (fieldsAt fixed dc ty)
  mInner <- for indexed \(i, dci) -> do
    xs <- freshFields dci aTy
    mAlts <- for indexed \(j, dcj) -> do
      ys <- freshFields dcj bTy
      if i /= j
        then pure (Just (Alt (DataAlt dcj) ys (mismatch i j), []))
        else do
          mops <- sequence (zipWith4 fieldOp [0 :: Int ..] (fieldsAt fixed dci aTy) xs ys)
          case sequence mops of
            Nothing  -> pure Nothing
            Just ows -> do
              body <- combine (map fst ows)
              pure (Just (Alt (DataAlt dcj) ys body, concatMap snd ows))
    case sequence mAlts of
      Nothing     -> pure Nothing
      Just altWss -> do
        let (alts, wss) = unzip altWss
        cbB <- freshId innerB "cbb"
        pure (Just ( Alt (DataAlt dci) xs
                       (destructInner fTc (fixed ++ [bTy]) (Cast (Var fbId) (coAt bTy)) cbB resTy alts)
                   , concat wss ))
  case sequence mInner of
    Nothing     -> pure Nothing
    Just altWss -> do
      let (alts, wss) = unzip altWss
      cbA <- freshId innerA "cba"
      pure (Just ( destructInner fTc (fixed ++ [aTy]) (Cast (Var faId) (coAt aTy)) cbA resTy alts
                 , concat wss ))

-- | Solve @C (Stock Inner)@ by building the dictionary from @Inner@'s
-- constructors.  We only act on the @Stock@ newtype, so unrelated code is
-- never affected.  @Eq@ handles any single-level algebraic type; @Ord@ is
-- limited to enumerations; anything else gets a clear "not implemented" error.
-- | A solver for one wrapper: 'Just' the 'Attempt' if it owns the wrapper (even
-- an error it reports), or 'Nothing' to defer to the next.  The Monoid is
-- first-success, so dispatch is a composition @stockSolver \<\> …@ — and a
-- companion solver would be just one more element.
-- The first-success Monoid is exactly @Alt (MaybeT m)@ (the Alternative-as-
-- Monoid that stops at the first solver returning a result), under the reader
-- arrows — so we derive it rather than hand-write it.
newtype Solver = Solver
  { runSolver :: PluginState -> Ct -> Class -> Type -> TcPluginM (Maybe Attempt) }
  deriving (Semigroup, Monoid)
    via (PluginState -> Ct -> Class -> Type -> Mon.Alt (MaybeT TcPluginM) Attempt)

notImplemented :: PluginState -> Ct -> SDoc -> TcPluginM Attempt
notImplemented st ct doc = do
  let key = showSDocUnsafe doc
  seen <- tcPluginIO (readIORef (psSeen st))
  unless (key `elem` seen) $ do
    tcPluginIO (modifyIORef' (psSeen st) (key :))
    unsafeTcPluginTcM (addErrTc (mkTcRnUnknownMessage (mkPlainError noHints doc)))
  pure (Nothing, [], [ct])

-- | A fresh local binder of the given type.
freshId :: Type -> String -> TcPluginM Id
freshId ty s = do
  u <- unsafeTcPluginTcM getUniqueM
  pure (mkLocalId (mkSystemName u (mkVarOcc s)) manyDataConTy ty)

-- | Build @compare :: wrapped -> wrapped -> Ordering@ for any single-level
-- algebraic type, matching derived @Ord@: compare constructor tags first, and
-- for the same constructor compare the fields lexicographically.  Field
-- comparisons use each field type's own @Ord@ (requested as wanted
-- constraints); the wanteds are returned alongside the expression.
toDatatype :: Type -> Repr -> Datatype
toDatatype via repr = Datatype
  { dtVia    = via
  , dtUnwrap = rCo repr
  , dtType   = rInner repr
  , dtCons   = [ Constructor dc (ciFields ci) defaultFixity labels (ciFieldCos ci)
               | ci <- rCons repr
               , let dc  = ciCon ci
                     fls = dataConFieldLabels dc
                     labels = if null fls then Nothing else Just fls ]
  }

-- | Run a @Deriver@ (built-in or discovered) as a solve attempt.
runDeriverAttempt :: Deriver -> Ct -> Class -> Datatype -> TcPluginM Attempt
runDeriverAttempt drv ct cls dt = do
  (ev, ws) <- runSynth (ctLoc ct) (runDeriver drv cls dt)
  pure (Just (ev, ct), ws, [])

-- | Discovery + dynamic loading (the extension mechanism): if a companion
-- package provides @instance DeriveStock C@, find it in the instance
-- environment, load its @Deriver@ value with GHC's plugin loader, and run it —
-- so a new class becomes derivable @via Stock@ just by depending on the
-- companion, with no change to the user's @-fplugin@ line.
tryWitness :: PluginState -> Ct -> Class -> Datatype -> TcPluginM (Maybe Attempt)
tryWitness st ct cls dt =
  case geWitness (psGen st) of
    Nothing     -> pure Nothing
    Just witCls -> do
      instEnvs <- getInstEnvs
      let clsTy   = mkTyConTy (classTyCon cls)
          matches = [ inst | inst <- classInstances instEnvs witCls
                           , [headTy] <- [is_tys inst], headTy `eqType` clsTy ]
      case matches of
        []         -> pure Nothing
        (inst : _) -> do
          let dfun = is_dfun inst
          hsc <- getTopEnv
          -- @DeriveStock@ is single-method with no superclass, so its dictionary
          -- is represented exactly as a @Deriver@; load the dfun at its own type
          -- and treat it as one.
          r <- unsafeTcPluginTcM $ liftIO $
                 getValueSafely hsc (idName dfun) (idType dfun)
          case r of
            Right (drv, _, _) -> Just <$> runDeriverAttempt drv ct cls dt
            Left _            -> pure Nothing

-- | The @Stock1@ counterpart of 'tryWitness': discover a companion
-- @instance DeriveStock1 C@, load its 'Deriver1', and run it on the inner
-- type constructor @f@.  (@deriving C via Stock1 F@ for a lifted @C@.)
tryWitness1 :: PluginState -> Ct -> Class -> Type -> Type -> TcPluginM (Maybe Attempt)
tryWitness1 st ct cls wrappedTy f =
  case geWitness1 (psGen st) of
    Nothing     -> pure Nothing
    Just witCls -> do
      instEnvs <- getInstEnvs
      let clsTy   = mkTyConTy (classTyCon cls)
          matches = [ inst | inst <- classInstances instEnvs witCls
                           , [headTy] <- [is_tys inst], headTy `eqType` clsTy ]
      case matches of
        []         -> pure Nothing
        (inst : _) -> do
          let dfun = is_dfun inst
          hsc <- getTopEnv
          r <- unsafeTcPluginTcM $ liftIO $
                 getValueSafely hsc (idName dfun) (idType dfun)
          case r of
            Right (Deriver1 synth, _, _) -> do
              m <- synth cls (ctLoc ct) wrappedTy f
              pure $ case m of
                Just (ev, ws) -> Just (Just (ev, ct), ws, [])
                Nothing       -> Nothing
            Left _ -> pure Nothing

-- | The @Stock2@ counterpart of 'tryWitness1': discover @instance DeriveStock2
-- C@ and run its 'Deriver2' on the inner two-parameter constructor @p@.
tryWitness2 :: PluginState -> Ct -> Class -> Type -> Type -> TcPluginM (Maybe Attempt)
tryWitness2 st ct cls wrappedTy p =
  case geWitness2 (psGen st) of
    Nothing     -> pure Nothing
    Just witCls -> do
      instEnvs <- getInstEnvs
      let clsTy   = mkTyConTy (classTyCon cls)
          matches = [ inst | inst <- classInstances instEnvs witCls
                           , [headTy] <- [is_tys inst], headTy `eqType` clsTy ]
      case matches of
        []         -> pure Nothing
        (inst : _) -> do
          let dfun = is_dfun inst
          hsc <- getTopEnv
          r <- unsafeTcPluginTcM $ liftIO $
                 getValueSafely hsc (idName dfun) (idType dfun)
          case r of
            Right (Deriver2 synth, _, _) -> do
              m <- synth cls (ctLoc ct) wrappedTy p
              pure $ case m of
                Just (ev, ws) -> Just (Just (ev, ct), ws, [])
                Nothing       -> Nothing
            Left _ -> pure Nothing

-- | @Eq@, re-expressed through the public SDK (@Datatype@ \/ @Synth@ \/ 'field')
-- rather than the bespoke @synthEq@ — a proof that the extension interface is
-- expressive enough to host a real, field-recursive synthesizer.  Produces the
-- same Core as @synthEq@.
conPrec :: DataCon -> TcPluginM Integer
conPrec dc = do
#if MIN_VERSION_ghc(9,12,0)
  Fixity p _ <- unsafeTcPluginTcM (lookupFixityRn (dataConName dc))
#else
  Fixity _ p _ <- unsafeTcPluginTcM (lookupFixityRn (dataConName dc))
#endif
  pure (fromIntegral p)

-- | The default-method Id for the i-th method of a class (for filling
-- dictionary fields we don't override, via a recursive dictionary).
defMethId :: Class -> Int -> TcPluginM Id
defMethId cls i =
  case snd (classOpItems cls !! i) of
    Just (nm, _) -> tcLookupId nm
    Nothing      -> error "stock: expected a default method"

-- | Synthesize an @Enum@ dictionary for an enumeration, mirroring GHC's
-- derived @Enum@: @fromEnum@ is the constructor tag, @toEnum@ uses
-- @tagToEnum#@.  @succ@/@pred@/@enumFromTo@/@enumFromThenTo@ come from the
-- class default methods (correct and bounded); @enumFrom@/@enumFromThen@ are
-- overridden to stop at the last constructor (the defaults would run to
-- @maxBound::Int@ and crash).
data Variance = Cov | Con

flipV :: Variance -> Variance
flipV Cov = Con
flipV Con = Cov

-- | Build a variance-correct mapper for a field type @t@ between @t[pv:=src]@
-- and @t[pv:=tgt]@ (where @src@\/@tgt@ are the actual @a@\/@b@ types).  This is
-- GHC's @DeriveFunctor@ algorithm: recurse through function arrows flipping
-- variance, and through covariant functor (or contravariant) applications.
--
--   * @Cov t@ yields @t[src] -> t[tgt]@; @Con t@ yields @t[tgt] -> t[src]@.
--   * the bare parameter maps via @covFwd@ (resp. @conFwd@); the unavailable
--     direction is 'Nothing', so a parameter in the wrong position fails
--     cleanly (e.g. a bare @a@ in a negative position is not a 'Functor').
--   * @fmapCls@ supplies @fmap@ for covariant subfields; @mContraCls@, if given,
--     supplies @contramap@ for contravariant subfields.
varMap :: Class -> Maybe Class -> CtLoc -> TyVar -> Type
       -> Maybe CoreExpr -> Maybe CoreExpr
       -> Variance -> Type -> TcPluginM (Maybe (CoreExpr, [Ct]))
varMap fmapCls mContraCls loc pv tgt covFwd conFwd =
  varMapN fmapCls mContraCls loc [(pv, tgt, covFwd, conFwd)] Nothing

-- | The n-ary variance engine behind 'varMap' (and so behind @Functor@,
-- @Contravariant@, @Bifunctor@, @Profunctor@, @Invariant@, …, which are this
-- one recursion at different /variance vectors/).  Each parameter carries its
-- own detection tyvar (the source instantiation it appears as in the field),
-- its target type, and the two directional mappers — @covFwd@ for a covariant
-- occurrence (a @src -> tgt@), @conFwd@ for a contravariant one (a @tgt ->
-- src@); the unavailable direction is 'Nothing', so a parameter used against
-- its declared variance fails cleanly.  A covariant slot populates @covFwd@
-- only, a contravariant slot @conFwd@ only, an invariant slot both.  The
-- recursion is GHC's @DeriveFunctor@ algorithm (arrows flip variance,
-- last-argument functor\/contravariant applications recurse), now substituting
-- /all/ parameters at once.
varMapN :: Class -> Maybe Class -> CtLoc
        -> [(TyVar, Type, Maybe CoreExpr, Maybe CoreExpr)]
        -> Maybe (Type -> TcPluginM (Maybe (CoreExpr, [Ct])))
        -> Variance -> Type -> TcPluginM (Maybe (CoreExpr, [Ct]))
varMapN fmapCls mContraCls loc params mSelf = go
  where
    fmapSel = classMethod "fmap" fmapCls
    pvs     = [ pv  | (pv, _, _, _)  <- params ]
    tgts    = [ tgt | (_, tgt, _, _) <- params ]
    sub t   = substTyWith pvs tgts t            -- t[srcs:=tgts]
    inA t   = any (`elemVarSet` tyCoVarsOfType t) pvs
    -- if @t@ is exactly one parameter's source tyvar, its directional mapper
    bareFwd t v = case [ (cf, conf) | (p, _, cf, conf) <- params, t `eqType` mkTyVarTy p ] of
      ((cf, conf) : _) -> Just (case v of Cov -> cf; Con -> conf)
      []               -> Nothing
    -- the spine of an application: @(head, [arg₁ .. argₖ])@
    spine ty = case splitAppTy_maybe ty of
      Just (f, a) -> let (h, as) = spine f in (h, as ++ [a])
      Nothing     -> (ty, [])
    -- a self-application @q src₁ .. srcₙ@: @q@ (the head applied to any leading
    -- fixed args) is parameter-free and the trailing @n@ args are exactly our
    -- @n@ source tyvars in order, so @q@'s own n-ary map (the same class we are
    -- deriving) carries it — e.g. a @pro a b@ field under @Profunctor@.
    matchSelf ty =
      let (h, args) = spine ty
          n         = length params
      in if length args >= n
           then let (pre, tl) = splitAt (length args - n) args
                    qhead     = mkAppTys h pre
                in if and (zipWith eqType tl (map mkTyVarTy pvs)) && not (inA qhead)
                     then Just qhead else Nothing
           else Nothing
    go v t
      | not (inA t) = do x <- freshId t "x"; pure (Just (Lam x (Var x), []))  -- id
      | Just mfwd <- bareFwd t v = pure (fmap (\e -> (e, [])) mfwd)
      | Just (_, _, s, r) <- splitFunTy_maybe t = do
          ms <- go (flipV v) s                  -- argument flips variance
          mr <- go v r
          case (ms, mr) of
            (Just (es, w1), Just (er, w2)) -> do
              let (sf, rf) = case v of Cov -> (s, r); Con -> (sub s, sub r)
                  xTy      = case v of Cov -> sub s; Con -> s
              g <- freshId (mkVisFunTyMany sf rf) "g"
              x <- freshId xTy "x"
              pure (Just (mkLams [g, x] (App er (App (Var g) (App es (Var x)))), w1 ++ w2))
            _ -> pure Nothing
      -- tuple: the one place the parameter may appear in several arguments —
      -- GHC's @ft_tup@ maps every component pointwise (not via @Bifunctor@):
      -- @\\(x1,..,xn) -> (m1 x1, .., mn xn)@.
      | Cov <- v, Just (tc, args) <- splitTyConApp_maybe t
      , isTupleTyCon tc, length args >= 2 = do
          ms <- mapM (go Cov) args
          case sequence ms of
            Nothing    -> pure Nothing
            Just pairs -> do
              let (mappers, wss) = unzip pairs
                  dc   = tupleDataCon Boxed (length args)
              xs  <- mapM (`freshId` "u") args
              tup <- freshId t "tup" ; cb <- freshId t "cb"
              let body = mkCoreConApps dc (map (Type . sub) args ++ zipWith App mappers (map Var xs))
              pure (Just (Lam tup (Case (Var tup) cb (sub t) [Alt (DataAlt dc) xs body]), concat wss))
      | Just self <- mSelf, Cov <- v, Just q <- matchSelf t = self q
      | Just (h, larg) <- splitAppTy_maybe t, not (inA h) = do
          mf <- go v larg                       -- try H as a covariant functor
          case mf of
            Just (e, w) -> do
              ev <- newWanted loc (mkClassPred fmapCls [h])
              let (ft, tt) = case v of Cov -> (larg, sub larg); Con -> (sub larg, larg)
              pure (Just ( mkApps (Var fmapSel) [Type h, ctEvExpr ev, Type ft, Type tt, e]
                         , mkNonCanonical ev : w ))
            Nothing -> case mContraCls of        -- else try H as a contravariant functor
              Nothing -> pure Nothing
              Just contraCls -> do
                mc <- go (flipV v) larg
                case mc of
                  Nothing       -> pure Nothing
                  Just (e, w) -> do
                    ev <- newWanted loc (mkClassPred contraCls [h])
                    -- contramap :: (x->y) -> f y -> f x
                    let (xT, yT) = case v of Cov -> (sub larg, larg); Con -> (larg, sub larg)
                    pure (Just ( mkApps (Var (classMethod "contramap" contraCls))
                                   [Type h, ctEvExpr ev, Type xT, Type yT, e]
                               , mkNonCanonical ev : w ))
      | otherwise = pure Nothing

-- | Destructure a scrutinee of inner type @F instTys@ (already coerced to
-- @F instTys@) into per-constructor alternatives.  A @data@ type becomes a real
-- @Case@; a @newtype@ has no runtime constructor — its single \"constructor\" is
-- a zero-cost coercion — so we unwrap the one field with a cast instead (a
-- @DataAlt@ on a newtype is rejected by Core Lint).
destructInner :: TyCon -> [Type] -> CoreExpr -> Id -> Type -> [CoreAlt] -> CoreExpr
destructInner fTc instTys scrut cb resTy alts
  | isNewTyCon fTc
  , [Alt _ [x] body] <- alts
  = Let (NonRec x (Cast scrut (mkUnbranchedAxInstCo Representational
                                 (newTyConCo fTc) instTys []))) body
  | otherwise = Case scrut cb resTy alts

-- | Synthesize @Functor (Stock1 F)@ — the covariant instance of the shared
-- @synthMap1@ engine.
freshTyVar :: String -> TcPluginM TyVar
freshTyVar = freshTyVarK liftedTypeKind

-- | A fresh type variable of the given kind.
freshTyVarK :: Kind -> String -> TcPluginM TyVar
freshTyVarK k s = do
  u <- unsafeTcPluginTcM getUniqueM
  pure (mkTyVar (mkSystemName u (mkTyVarOcc s)) k)

-- | Extract the 'CoreExpr' from the @EvExpr@ forms we build.
unwrapEv :: EvTerm -> CoreExpr
unwrapEv (EvExpr e) = e
unwrapEv _          = error "stock: expected EvExpr"

-- ----- shared ReadPrec assembler (GHC-faithful Read / Read1 / Read2) -------
--
-- GHC's derived @Read@ defines @readPrec@ (not @readsPrec@); @readsPrec@ comes
-- from the class default @readPrec_to_S readPrec@.  Building the very same
-- @readPrec@ (same combinators, same @+++@ order) makes the synthesized
-- instance byte-faithful, including the order of ambiguous infix parses.

-- | Every combinator GHC's derived @readPrec@ uses, looked up once.
data ReadPrecEnv = ReadPrecEnv
  { rpReadPrecTc :: TyCon
  , rpMonadDict  :: CoreExpr
  , rpBindSel, rpThenSel, rpReturnSel :: Id
  , rpParens, rpChoose, rpExpectP, rpReadField :: Id
  , rpPrec, rpStep, rpReset, rpPlus, rpPfail :: Id
  , rpIdentCon, rpSymbolCon, rpPuncCon :: DataCon
  }

-- | Look up the @ReadPrec@ combinators and request a @Monad ReadPrec@ wanted
-- (returned as the second component, to be emitted alongside the synthesized
-- instance's other wanteds).
lookupReadPrecEnv :: CtLoc -> TcPluginM (ReadPrecEnv, Ct)
lookupReadPrecEnv loc = do
  monadCls    <- tcLookupClass monadClassName
  readPrecTc  <- lookupOrig tEXT_READPREC (mkTcOcc "ReadPrec") >>= tcLookupTyCon
  parensId    <- lookupOrig gHC_INTERNAL_READ (mkVarOcc "parens")    >>= tcLookupId
  chooseId    <- lookupOrig gHC_INTERNAL_READ (mkVarOcc "choose")    >>= tcLookupId
  expectPId   <- lookupOrig gHC_INTERNAL_READ (mkVarOcc "expectP")   >>= tcLookupId
  readFieldId <- lookupOrig gHC_INTERNAL_READ (mkVarOcc "readField") >>= tcLookupId
  precId      <- lookupOrig tEXT_READPREC (mkVarOcc "prec")  >>= tcLookupId
  stepId      <- lookupOrig tEXT_READPREC (mkVarOcc "step")  >>= tcLookupId
  resetId     <- lookupOrig tEXT_READPREC (mkVarOcc "reset") >>= tcLookupId
  plusId      <- lookupOrig tEXT_READPREC (mkVarOcc "+++")   >>= tcLookupId
  pfailId     <- lookupOrig tEXT_READPREC (mkVarOcc "pfail") >>= tcLookupId
  identCon    <- lookupOrig tEXT_READ_LEX (mkDataOcc "Ident")  >>= tcLookupDataCon
  symbolCon   <- lookupOrig tEXT_READ_LEX (mkDataOcc "Symbol") >>= tcLookupDataCon
  puncCon     <- lookupOrig tEXT_READ_LEX (mkDataOcc "Punc")   >>= tcLookupDataCon
  monadEv <- newWanted loc (mkClassPred monadCls [mkTyConTy readPrecTc])
  pure ( ReadPrecEnv readPrecTc (ctEvExpr monadEv)
           (classMethod ">>=" monadCls) (classMethod ">>" monadCls) (classMethod "return" monadCls)
           parensId chooseId expectPId readFieldId precId stepId resetId plusId pfailId
           identCon symbolCon puncCon
       , mkNonCanonical monadEv )

-- | Assemble a @readPrec@-shaped body for element type @gTy@.  Each constructor
-- carries one /raw/ field reader (a @ReadPrec ft@) per field; this wraps them
-- exactly as GHC: nullary cons grouped into one leading @choose@, then prefix
-- (@prec 10@ + @step@) \/ infix (@prec fixity@ + @step@) \/ record (@prec 11@ +
-- @readField name (reset _)@) cons in declaration order, all under @parens@.
-- @mkConVal dc binders@ builds the (already wrapped\/cast) constructor value.
buildReadPrecBody :: ReadPrecEnv -> Type -> (DataCon -> [Id] -> CoreExpr)
                  -> [(DataCon, [(Type, CoreExpr)])] -> TcPluginM CoreExpr
buildReadPrecBody env gTy mkConVal cons = do
  let ReadPrecEnv readPrecTc monadDict bindSel thenSel returnSel
        parensId chooseId expectPId readFieldId precId stepId resetId plusId pfailId
        identCon symbolCon puncCon = env
      readPrecTy    = mkTyConTy readPrecTc
      strPairTy     = mkBoxedTupleTy [stringTy, mkTyConApp readPrecTc [gTy]]
      bindP a b m k = mkApps (Var bindSel)   [Type readPrecTy, monadDict, Type a, Type b, m, k]
      thenP a b m n = mkApps (Var thenSel)   [Type readPrecTy, monadDict, Type a, Type b, m, n]
      returnP a v   = mkApps (Var returnSel) [Type readPrecTy, monadDict, Type a, v]
      seqW m n      = thenP unitTy gTy m n
      parensE a p   = mkApps (Var parensId) [Type a, p]
      precE a n p   = mkApps (Var precId)   [Type a, mkUncheckedIntExpr n, p]
      stepE a p     = mkApps (Var stepId)   [Type a, p]
      resetE a p    = mkApps (Var resetId)  [Type a, p]
      plusE a p q   = mkApps (Var plusId)   [Type a, p, q]
      chooseE a xs  = mkApps (Var chooseId) [Type a, xs]
      readFieldE a s p = mkApps (Var readFieldId) [Type a, s, p]
      expectPE l    = App (Var expectPId) l
      identE s  = mkCoreConApps identCon  [s]
      symbolE s = mkCoreConApps symbolCon [s]
      puncE s   = mkCoreConApps puncCon   [s]
      str s     = unsafeTcPluginTcM (mkStringExprFS (fsLit s))
  entries <- for cons \(dc, readers) -> do
    let name   = occNameString (getOccName dc)
        labels = map (occNameString . nameOccName . flSelector) (dataConFieldLabels dc)
    nameE  <- str name
    argIds <- zipWithM (\(ft, _) i -> freshId ft ("a" ++ show (i :: Int))) readers [0 ..]
    let ret   = returnP gTy (mkConVal dc argIds)
        items = zip3 argIds (map fst readers) (map snd readers)  -- (binder, ft, rawReader)
    if null readers
      then pure (Left (nameE, ret))                              -- nullary -> choose entry
      else if dataConIsInfix dc
        then do
          prec <- conPrec dc
          let [(a0, ft0, rd0), (a1, ft1, rd1)] = items
              inner = bindP ft0 gTy (stepE ft0 rd0) $ Lam a0 $
                      seqW (expectPE (symbolE nameE)) $
                      bindP ft1 gTy (stepE ft1 rd1) (Lam a1 ret)
          pure (Right (precE gTy prec inner))
      else if not (null labels)
        then do
          openCE <- str "{"; closeCE <- str "}"; commaCE <- str ","
          lblEs  <- mapM str labels
          let closeRet = seqW (expectPE (puncE closeCE)) ret
              go [] = closeRet
              go ((i, lblE, (aId, ft, rd)) : rest) =
                let bound = bindP ft gTy (readFieldE ft lblE (resetE ft rd)) (Lam aId (go rest))
                in if i == (0 :: Int) then bound else seqW (expectPE (puncE commaCE)) bound
              inner = seqW (expectPE (identE nameE)) $
                      seqW (expectPE (puncE openCE)) $
                      go (zip3 [0 ..] lblEs items)
          pure (Right (precE gTy 11 inner))
      else do                                                    -- prefix with args
        let chain = foldr (\(aId, ft, rd) acc -> bindP ft gTy (stepE ft rd) (Lam aId acc)) ret items
            inner = seqW (expectPE (identE nameE)) chain
        pure (Right (precE gTy 10 inner))
  let nullaries = [e | Left e  <- entries]
      others    = [p | Right p <- entries]
      chooseP   = chooseE gTy (mkListExpr strPairTy [ mkCoreTup [n, p] | (n, p) <- nullaries ])
      allP      = [chooseP | not (null nullaries)] ++ others
      combined  = case allP of
                    []  -> mkApps (Var pfailId) [Type gTy]
                    [p] -> p
                    ps  -> foldr1 (plusE gTy) ps
  pure (parensE gTy combined)
