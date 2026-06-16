{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin Stock #-}
module Main (main) where
import Stock (Stock(..), Stock1(..), Stock2(..))
import Stock.NFData (NFData(..), NFData1(..), NFData2(..))  -- class + registers DeriveStock(1,2)
import Stock.Override (Override(..), Overriding1, Overriding2, Override1(..), Override2(..), Keep, type (:=))
import Control.DeepSeq (deepseq)
import Control.Exception (try, evaluate, SomeException)

data T = T Int Bool | U deriving NFData via Stock T

-- NFData1's quantified superclass (forall a. NFData a => NFData (F a)) needs an
-- NFData (F a) instance too, exactly as Eq1 needs Eq.
data F a = F Int a [a]
  deriving NFData  via Stock (F a)
  deriving NFData1 via Stock1 F

-- NFData2 chains the superclasses: NFData (P a b), NFData1 (P a), NFData2 P.
data P a b = P a b [a]
  deriving NFData  via Stock (P a b)
  deriving NFData1 via Stock1 (P a)
  deriving NFData2 via Stock2 P

-- An observable modifier: @Lazily@ is a newtype over @[a]@ (so coercible to the
-- real field) whose 'NFData1' forces /nothing/.  Honoring Override is therefore
-- visible: an @undefined@ list element is never touched.
newtype Lazily a = Lazily [a]
instance NFData  (Lazily a) where rnf     _   = ()  -- NFData1's quantified superclass
instance NFData1 Lazily     where liftRnf _ _ = ()

-- NFData1 via Override1: the @[a]@ field is forced through @Lazily@.  (As with
-- @F@, NFData1's quantified superclass needs an @NFData (NL a)@ instance too.)
data NL a = NL [a]
  deriving NFData  via Stock (NL a)
  deriving NFData1 via Overriding1 NL '[ '[Lazily] ]

-- NFData2 via Override2: the @[a]@ field (first parameter) forced through
-- @Lazily@; the @b@ field kept.
data NL2 a b = NL2 [a] b
  deriving NFData  via Stock (NL2 a b)
  deriving NFData1 via Stock1 (NL2 a)
  deriving NFData2 via Overriding2 NL2 '[ '[Lazily, Keep] ]

-- value-level NFData via Override: @Lazy@ is a newtype over @Int@ whose @rnf@
-- forces nothing, so field 0 is never evaluated (an @undefined@ survives).
newtype Lazy = Lazy Int
instance NFData Lazy where rnf _ = ()
-- complex config (type-keyed): every @Int@ field forced through @Lazy@.
data NV = NV Int Bool
  deriving NFData via Stock (Override NV '[ Int := Lazy ])

-- True iff forcing does NOT blow up (i.e. Override was honored and the lazy
-- modifier skipped the bottom element).
survives :: () -> IO Bool
survives u = either (const False) (const True)
         <$> (try (evaluate u) :: IO (Either SomeException ()))

main :: IO ()
main = do
  ( T 1 True `deepseq` U
    `deepseq` liftRnf rnf (F 1 (2 :: Int) [3, 4])
    `deepseq` liftRnf2 rnf rnf (P (1 :: Int) 'c' [2, 3]) ) `seq` pure ()
  -- Override1: NL's [a] forced through Lazily, so the undefined survives.
  ok1 <- survives (liftRnf rnf (NL [undefined :: Int]))
  -- Override2: NL2's [a] forced through Lazily; the 'b' is still forced normally.
  ok2 <- survives (liftRnf2 rnf rnf (NL2 [undefined :: Int] 'c'))
  -- value Override: NV's Int field forced through Lazy (no-op), so undefined survives.
  ok3 <- survives (rnf (NV undefined True))
  if ok1 && ok2 && ok3
    then putStrLn "ok: NFData + NFData1 + NFData2 (incl. Override + Override1/2) via stock-deepseq"
    else error "Override not honored for NFData/NFData1/NFData2"
