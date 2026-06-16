{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin Stock #-}
module Main (main) where

import Stock (Stock2(..))
import Stock.Profunctor (Profunctor(..))    -- class + registers DeriveStock2 Profunctor
import Stock.Override (Overriding2, Override2(..), Keep, type (:=))
import Control.Arrow (Kleisli(..))
import System.Exit (exitFailure)
import Control.Monad (unless)

-- the function profunctor field: dimap pre/post-composes
newtype Hom a b = Hom (a -> b)
  deriving Profunctor via Stock2 Hom

runHom :: Hom a b -> a -> b
runHom (Hom f) = f

-- a product: an arrow field (contravariant a, covariant b), a covariant [b],
-- and a constant.  dimap f g = (compose f/g into the arrow, map g over [b],
-- keep the Int).
data P a b = P (a -> b) [b] Int
  deriving Profunctor via Stock2 P

runP :: P a b -> (a -> b, [b], Int)
runP (P f bs n) = (f, bs, n)

-- a NESTED profunctor field: Kleisli Maybe a b = q a b — handled by recursing
-- through Kleisli's own dimap (the self-application case in the engine).
newtype Nest a b = Nest (Kleisli Maybe a b)
  deriving Profunctor via Stock2 Nest

runNest :: Nest a b -> a -> Maybe b
runNest (Nest (Kleisli f)) = f

-- Profunctor via Override2: the covariant [b] field is reshaped to RevL, whose
-- fmap reverses — so dimap maps g over the list AND reverses it (observably
-- different from plain []).  The arrow field is kept.
newtype RevL a = RevL [a]
instance Functor RevL where fmap f (RevL xs) = RevL (reverse (map f xs))
-- complex config (field-keyed): the covariant @poList@ field reshaped to RevL.
data PO a b = PO { poFn :: a -> b, poList :: [b] }
  deriving Profunctor via Overriding2 PO '[ poList := RevL ]
runPO :: PO a b -> (a -> b, [b])
runPO (PO f bs) = (f, bs)

main :: IO ()
main = do
  let -- dimap (+1) (*2) (Hom (*10)) :: a=3 -> (+1)=4 -> (*10)=40 -> (*2)=80
      d  = runHom (dimap (+ 1) (* 2) (Hom (* 10)) :: Hom Int Int) 3 == 80
      -- lmap f = dimap f id ;  rmap g = dimap id g
      l  = runHom (lmap (+ 1) (Hom (* 10)) :: Hom Int Int) 3 == 40
      r  = runHom (rmap (* 2) (Hom (* 10)) :: Hom Int Int) 3 == 60
      (pf, pbs, pn) = runP (dimap (+ 1) (* 2) (P (* 10) [1, 2, 3] 7) :: P Int Int)
      p  = pf 3 == 80 && pbs == [2, 4, 6] && pn == 7
      -- nested Kleisli Maybe field: dimap (+1) (*2) over Nest (\b -> Just (b*10))
      -- a=3 -> (+1)=4 -> Kleisli=Just 40 -> fmap (*2)=Just 80
      n  = runNest (dimap (+ 1) (* 2) (Nest (Kleisli (\b -> Just (b * 10)))) :: Nest Int Int) 3
             == Just 80
      -- Override2: [b] reshaped to RevL ⇒ dimap maps (*2) AND reverses the list
      (of_, obs) = runPO (dimap (+ 1) (* 2) (PO (* 10) [1, 2, 3]) :: PO Int Int)
      o  = of_ 3 == 80 && obs == [6, 4, 2]    -- reversed, not [2,4,6]
  unless (and [d, l, r, p, n, o]) exitFailure
  putStrLn "ok: Profunctor (dimap/lmap/rmap, nested q a b, Override2) via stock-profunctors"
