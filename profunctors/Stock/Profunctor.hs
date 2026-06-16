{-# LANGUAGE CPP #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-orphans #-}   -- the @DeriveStock2@ registration is necessarily an orphan

-- | A companion \"solver\" package teaching the @stock@ plugin to derive
-- @Profunctor@ (from @profunctors@) without being a plugin itself.
--
-- @Profunctor@ is the @[Contra, Co]@ instance of the plugin's /n-ary variance
-- functor/ engine ('Stock.Internal.varMapN') — the very same recursion behind
-- @Functor@ @[Co]@, @Contravariant@ @[Contra]@ and @Bifunctor@ @[Co, Co]@.  So
-- @dimap@ is built by walking each field with the first parameter marked
-- contravariant and the second covariant: a function field @a -> b@ pre\/post
-- composes, a covariant @b@\/@h b@ field maps forward, constants are kept.
--
-- Downstream: @data P a b = … deriving Profunctor via Stock2 P@; just depend on
-- @stock-profunctors@, no extra @-fplugin@.
module Stock.Profunctor (Profunctor(..)) where

import GHC.Plugins
import GHC.Core.Class (classMethods)
import GHC.Core.Predicate (mkClassPred)
import GHC.Tc.Plugin (newWanted, tcLookupClass)
import GHC.Tc.Types.Constraint (ctEvExpr, mkNonCanonical)
import GHC.Tc.Types.Evidence (EvTerm(EvExpr))
import GHC.Core.Multiplicity (scaledThing)
import GHC.Builtin.Names (functorClassName)
import Control.Monad (forM, zipWithM)
import Data.Profunctor (Profunctor(..))
import Stock.Derive
import Stock.Internal  -- 'reshapeCo' / 'castReshape' (field reshape) come from here
import Stock.Bifunctor (BiField(..), classifyBiField)

-- | @dimap :: (a -> b) -> (c -> d) -> p b c -> p a d@ — synthesized by 'varMapN'
-- at the variance vector @[Contra, Co]@.  The first parameter's source
-- instantiation is @b@ (the input is @p b c@) with @f :: a -> b@ as its
-- /contravariant/ mapper; the second's is @c@ with @g :: c -> d@ as its
-- /covariant/ mapper.  Each constructor is rebuilt at @(a, d)@.
instance DeriveStock2 Profunctor where
  deriveStock2 :: Deriver2
  deriveStock2 = Deriver2 \proCls loc wrappedTy p -> do
    tcs   <- lookupOvTcs "Override2"
    -- @p@ may be @Override2 cfg realP@ (positional or field-keyed): peel it (else
    -- 'varMapN' would treat the wrapper as a nested @pro a b@ field and recurse).
    let mOv2 = ovWrap tcs ; mKeep = ovKeep tcs
        (realP, mMods) = peelOverride2With tcs p
    case (tyConAppTyCon_maybe wrappedTy, tyConAppTyCon_maybe realP) of
      (Just st2Tc, Just pTc) -> do
        functorCls <- tcLookupClass functorClassName
        let fixed      = tyConAppArgs realP
            dcons      = tyConDataCons pTc
            dimapIdx   = case [ i | (i, m) <- zip [0 :: Int ..] (classMethods proCls)
                                  , occNameString (getOccName m) == "dimap" ] of
                           (i : _) -> i
                           []      -> 0
            coAt t1 t2 = coDown2With mOv2 st2Tc wrappedTy p realP t1 t2
        -- dimap :: forall a b c d. (a -> b) -> (c -> d) -> p b c -> p a d
        aTv <- freshTyVar "a" ; bTv <- freshTyVar "b"
        cTv <- freshTyVar "c" ; dTv <- freshTyVar "d"
        let aTy = mkTyVarTy aTv ; bTy = mkTyVarTy bTv
            cTy = mkTyVarTy cTv ; dTy = mkTyVarTy dTv
        fId <- freshId (mkVisFunTyMany aTy bTy) "f"               -- a -> b (contravariant slot)
        gId <- freshId (mkVisFunTyMany cTy dTy) "g"               -- c -> d (covariant slot)
        tId <- freshId (mkAppTy (mkAppTy wrappedTy bTy) cTy) "t"  -- p b c
        cb  <- freshId (mkTyConApp pTc (fixed ++ [bTy, cTy])) "cb"
        let dimapSel = classMethod "dimap" proCls
            -- per parameter: (source tyvar, target, covFwd, conFwd)
            params = [ (bTv, aTy, Nothing,         Just (Var fId))    -- Contra: f used negatively
                     , (cTv, dTy, Just (Var gId), Nothing) ]          -- Co:     g used positively
            resTy  = mkAppTy (mkAppTy wrappedTy aTy) dTy             -- p a d
            -- a nested @pro a b@ field: recurse via @pro@'s own @dimap@ (the
            -- same [Contra, Co] shape), so e.g. a @Kleisli m a b@ field works.
            selfPro q = do
              ev <- newWanted loc (mkClassPred proCls [q])
              pure (Just ( mkApps (Var dimapSel)
                             [ Type q, ctEvExpr ev, Type aTy, Type bTy, Type cTy, Type dTy
                             , Var fId, Var gId ]
                         , [mkNonCanonical ev] ))
            mapPlain x ft = do
              m <- varMapN functorCls Nothing loc params (Just selfPro) Cov ft
              pure (fmap (\(e, ws) -> (App e (Var x), ws)) m)
            -- under @Override2@, a covariant @h c@ field is reshaped to @mod c@:
            -- map @c -> d@ through @mod@'s @fmap@ on the coerced value, coerce back.
            mapField i x ft = case (override1ModWith mKeep mMods i, classifyBiField bTv cTv bTy cTy ft) of
              (Just mod_, Just (BFFoldB h)) -> do
                m <- varMapN functorCls Nothing loc params (Just selfPro) Cov (mkAppTy mod_ cTy)
                pure $ flip fmap m \(e, ws) ->
                  ( Cast (App e (castReshape (Var x) (reshapeCo h mod_ cTy))) (mkSymCo (reshapeCo h mod_ dTy)), ws )
              _ -> mapPlain x ft
        malts <- forM dcons \dc -> do
          let fts = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [bTy, cTy]))
          xs  <- zipWithM (\n ft -> freshId ft ("x" ++ show n)) [0 :: Int ..] fts
          mfs <- sequence (zipWith3 mapField [0 :: Int ..] xs fts)
          case sequence mfs of
            Nothing    -> pure Nothing
            Just pairs ->
              let (vals, wss) = unzip pairs
                  body = Cast (mkCoreConApps dc (map Type (fixed ++ [aTy, dTy]) ++ vals))
                              (mkSymCo (coAt aTy dTy))             -- p a d -> Stock2 P a d
              in pure (Just (Alt (DataAlt dc) xs body, concat wss))
        case sequence malts of
          Nothing     -> pure Nothing
          Just altWss -> do
            let (alts, wss) = unzip altWss
                impl = mkLams [aTv, bTv, cTv, dTv, fId, gId, tId]
                         (destructInner pTc (fixed ++ [bTy, cTy])
                            (Cast (Var tId) (coAt bTy cTy)) cb resTy alts)
            -- supply dimap; lmap / rmap / (#.) / (.#) come from the class defaults
            dict <- recDictWith proCls wrappedTy [] [(dimapIdx, impl)]
            pure (Just (EvExpr dict, concat wss))
      _ -> pure Nothing
