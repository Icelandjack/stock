{-# LANGUAGE RankNTypes #-}
-- | Source-level sugar for "Stock.Override": a @parsedResultAction@ that lowers
-- the lowercase, no-backtick surface
--
-- > Override [ x via Sum, Coord at 0 via Sum ] T
--
-- into the honest marker form the type-checker plugin reads
--
-- > Override [ "x" := Sum, At Coord 0 := Sum ] T
--
-- keeping a single infix operator (@:=@); @at@ becomes the prefix marker @At@,
-- and a bare lowercase selector becomes a 'Symbol' literal.  The rewrite is
-- /scoped to @Override@ applications/, runs before renaming, and reuses the
-- original sub-trees (so spans survive); @via@\/@at@ elsewhere are untouched.
-- Enabled by the same @-fplugin Stock@ as the solver.
module Stock.Surface (lowerOverrides) where

import GHC.Plugins
import GHC.Hs
import GHC.Types.SourceText (SourceText(NoSourceText))
import Data.Char (isLower)
import Data.Data (Data, gmapT)
import Data.Typeable (Typeable, cast)
import Data.Maybe (fromMaybe)

-- A two-line slice of @syb@ over @base@'s 'Data'/'Typeable' (the GHC AST derives
-- 'Data'), so we depend on no extra package.

-- | Apply @f@ at every subterm, bottom-up.  An endofunction on the type of
-- type-preserving polymorphic transformations.
everywhere :: (forall x. Data x => x -> x) -> (forall x. Data x => x -> x)
everywhere f = f . gmapT (everywhere f)

-- | Lift a single-type transformation to act only where the type matches.
mkT :: (Typeable a, Typeable b) => (b -> b) -> a -> a
mkT f = fromMaybe id (cast f)

-- | Rewrite every @Override [ … ]@ config in the parsed module.
lowerOverrides :: ParsedResult -> ParsedResult
lowerOverrides pr =
  pr { parsedResultModule =
         let m = parsedResultModule pr
         in m { hpm_module = everywhere (mkT rewriteTy) (hpm_module m) } }

-- | If this type is @Override T CFG@ (or the @Overriding@\/@Overriding1@\/
-- @Overriding2@ synonyms — all type-first), lower the entries of @CFG@.  @CFG@
-- is the /last/ argument here (the wrappers are type-first: @Overriding T cfg@).
rewriteTy :: HsType GhcPs -> HsType GhcPs
rewriteTy ty
  | HsAppTy x f cfg <- ty            -- (hd T) cfg
  , L _ (HsAppTy _ hd _) <- f        -- f = hd T
  , Just mq <- overrideHeadQual (unLoc hd)
  , Just cfg' <- lowerConfig mq cfg
  = HsAppTy x f cfg'                 -- keep @hd T@, lower the config
  | otherwise = ty

-- | If this is an @Override@-family head, report /how it was qualified/ — the
-- module alias if written @S.Override@ (@import Stock.Override qualified as S@),
-- or 'Nothing' if unqualified.  The generated markers (@:=@, @At@, @Keep@) mirror
-- this, so they resolve no matter how the user imported "Stock.Override".
overrideHeadQual :: HsType GhcPs -> Maybe (Maybe ModuleName)
overrideHeadQual (HsTyVar _ _ (L _ rdr))
  | occNameString (rdrNameOcc rdr) `elem`
      ["Override", "Overriding", "Overriding1", "Overriding2"]
  = Just (fst <$> isQual_maybe rdr)
overrideHeadQual _ = Nothing

-- | Build a marker constructor name (@:=@, @At@, @Keep@), qualified the same way
-- the @Override@ head was, so it is in scope under any import style.
mkMarker :: Maybe ModuleName -> String -> RdrName
mkMarker Nothing  nm = mkRdrUnqual (mkTcOcc nm)
mkMarker (Just m) nm = mkRdrQual m  (mkTcOcc nm)

-- | Lower a config list by rewriting each element.  The config is assumed to be
-- an actual type-level list ('HsExplicitListTy') — i.e. @'[ … ]@, or @[ … ]@
-- under @NoListTuplePuns@.  A single-element @[a]@ that parses as the /list
-- type/ is deliberately /not/ reinterpreted (write @'[a]@ instead).
--
-- Two surfaces share this pass: the entry-list form (each element lowered by
-- 'lowerEntry'), and the positional @'[ '[m, _, …] ]@ form whose inner lists
-- carry the @_@ no-op — every type wildcard anywhere in the config is lowered
-- to the @Keep@ marker that the solver reads.
lowerConfig :: Maybe ModuleName -> LHsType GhcPs -> Maybe (LHsType GhcPs)
lowerConfig mq (L l (HsExplicitListTy x p es)) =
  Just (everywhere (mkT (wildToKeep mq)) (L l (HsExplicitListTy x p (map (lowerEntry mq) es))))
lowerConfig _ _ = Nothing

-- | The positional no-op: a type wildcard @_@ ('HsWildCardTy') becomes the
-- @Keep@ marker, qualified to match the @Override@ head.  (Bare @Keep@ written by
-- hand is left as-is.)
wildToKeep :: Maybe ModuleName -> HsType GhcPs -> HsType GhcPs
wildToKeep mq (HsWildCardTy _) =
  unLoc (nlHsTyVar NotPromoted (mkMarker mq "Keep"))
wildToKeep _ t = t

-- | Lower one entry.  Surfaces:
--
--   * @sel via modifier@ — split the application spine on @via@, rebuild as
--     @(:=) selector modifier@.
--   * @sel via a -> f b@ — @via@ binds looser than @->@: GHC parses this as
--     @(sel via a) -> f b@, so we peel @via@ off the /domain/ and rebuild the
--     modifier as @a -> f b@ (i.e. @sel via (a -> f b)@ without the parens).
--   * @sel := modifier@  — written with the operator directly; lower only the
--     /selector/ (the LHS).
--
-- Anything else is left untouched.
lowerEntry :: Maybe ModuleName -> LHsType GhcPs -> LHsType GhcPs
lowerEntry mq (L l (HsOpTy x prom lhs op rhs))
  | isVarRdr ":=" (unLoc op) =
      L l (HsOpTy x prom (lowerSelector mq (spine lhs)) op rhs)
lowerEntry mq (L l (HsFunTy x arr dom cod))
  | (sel@(_ : _), _via : modAtoms@(_ : _)) <- break (isVar "via") (spine dom) =
      mkPrefix mq ":=" [lowerSelector mq sel, L l (HsFunTy x arr (reassemble modAtoms) cod)]
lowerEntry mq e =
  case break (isVar "via") (spine e) of
    (sel@(_ : _), _via : modAtoms@(_ : _)) ->
      mkPrefix mq ":=" [lowerSelector mq sel, reassemble modAtoms]
    _ -> e

-- | The selector left of @via@: @con at pos@ ⇒ @At con pos@; a bare lowercase
-- head ⇒ a 'Symbol' literal; otherwise reassembled as a type (type-keyed).
lowerSelector :: Maybe ModuleName -> [LHsType GhcPs] -> LHsType GhcPs
lowerSelector mq atoms =
  case break (isVar "at") atoms of
    (con@(_ : _), _at : pos@(_ : _)) ->
      mkPrefix mq "At" [nameOrType con, reassemble pos]
    _ -> nameOrType atoms

-- | A single bare lowercase variable ⇒ field-name 'Symbol' literal; else a type.
nameOrType :: [LHsType GhcPs] -> LHsType GhcPs
nameOrType [L l (HsTyVar _ NotPromoted (L _ rdr))]
  | isLowerName rdr =
      L l (HsTyLit noExtField (HsStrTy NoSourceText (occNameFS (rdrNameOcc rdr))))
nameOrType atoms = reassemble atoms

-- ----- application-spine helpers -------------------------------------------

-- | Flatten a left-nested @HsAppTy@ into its atoms (head first).
spine :: LHsType GhcPs -> [LHsType GhcPs]
spine (L _ (HsAppTy _ f a)) = spine f ++ [a]
spine t                     = [t]

-- | Re-nest a non-empty atom list into a left-associated application.
reassemble :: [LHsType GhcPs] -> LHsType GhcPs
reassemble = foldl1 mkHsAppTy

-- | Prefix application of a marker type constructor named @nm@ to @args@,
-- qualified to match the @Override@ head (see 'mkMarker').
mkPrefix :: Maybe ModuleName -> String -> [LHsType GhcPs] -> LHsType GhcPs
mkPrefix mq nm = foldl mkHsAppTy (nlHsTyVar NotPromoted (mkMarker mq nm))

-- ----- predicates ----------------------------------------------------------

isVar :: String -> LHsType GhcPs -> Bool
isVar nm (L _ (HsTyVar _ _ (L _ rdr))) = isVarRdr nm rdr
isVar _  _                             = False

isVarRdr :: String -> RdrName -> Bool
isVarRdr nm rdr = occNameString (rdrNameOcc rdr) == nm

isLowerName :: RdrName -> Bool
isLowerName rdr = case occNameString (rdrNameOcc rdr) of
  (c : _) -> isLower c
  _       -> False
