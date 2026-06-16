#!/usr/bin/env bash
# Should-fail harness for per-field Override validation.
#
# A reshape `field via M` is only sound when `field` is coercible to the
# modifier `M` applied to the parameters.  The plugin emits a GHC-checked
# `Coercible` wanted for every reshape, so an INVALID override must be a
# compile error.  This can't be expressed in a normal module (the module
# wouldn't compile), so we compile each snippet with the plugin and assert the
# expected outcome.  Negative cases MUST fail; positive controls MUST compile
# (so a regression that makes the plugin reject *everything* is also caught).
#
# Run from anywhere:  bash negative/run-negative.sh
set -u
[ -d "$HOME/.ghcup/bin" ] && export PATH="$HOME/.ghcup/bin:$PATH"
cd "$(dirname "$0")/.."                       # project root
cabal build stock >/dev/null 2>&1 || { echo "stock failed to build"; exit 2; }

TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
PRE='{-# OPTIONS_GHC -fplugin Stock #-}
{-# LANGUAGE DerivingVia, DataKinds, TypeOperators, StandaloneDeriving, FlexibleContexts, UndecidableInstances, TypeFamilies #-}
module N where
import Stock
import Control.Category
import Control.Arrow (Kleisli(..))
import Control.Applicative (ZipList(..))
import Data.Functor.Classes (Eq1(..))
import Data.Bifunctor
import Prelude hiding (id, (.))
newtype Op cat a b = Op (cat b a)
instance Category cat => Category (Op cat) where { id = Op id; Op f . Op g = Op (g . f) }
newtype Basic m a b = Basic m
instance Monoid m => Category (Basic m) where { id = Basic mempty; Basic a . Basic b = Basic (a <> b) }'

fails=0
# check NAME EXPECT BODY    where EXPECT = reject | accept
check () {
  local name="$1" expect="$2" body="$3"
  printf '%s\n%s\n' "$PRE" "$body" > "$TMP/N.hs"
  if cabal exec -- ghc -O0 -fno-code -package stock -fforce-recomp "$TMP/N.hs" >/dev/null 2>&1
  then got=accept; else got=reject; fi
  if [ "$got" = "$expect" ]; then
    printf 'ok   %-46s (%s)\n' "$name" "$expect"
  else
    printf 'FAIL %-46s expected %s, got %s\n' "$name" "$expect" "$got"; fails=$((fails+1))
  fi
}

echo "== negative: invalid reshapes MUST be rejected =="
check "Functor  Maybe via []"        reject "data A a = A (Maybe a) deriving Functor                via Overriding1 A '[ '[ [] ] ]"
check "Foldable Maybe via []"        reject "data B a = B (Maybe a) deriving Foldable               via Overriding1 B '[ '[ [] ] ]"
check "Applicative Maybe via []"     reject "data C a = C (Maybe a) deriving (Functor,Applicative)  via Overriding1 C '[ '[ [] ] ]"
check "Eq Int via Bool"              reject "data E = E Int deriving (Eq,Show)                       via Stock (Override E '[ Int via Bool ])"
check "Category Int via Op (->)"     reject "data T1 a b = T1 { z :: Int } deriving Category         via Overriding2 T1 '[ T1 at 0 via Op (->) ]"
check "Category a->b via Op (->)"    reject "data T2 a b = T2 { f :: a -> b } deriving Category      via Overriding2 T2 '[ T2 at 0 via Op (->) ]"

echo "== positive controls: valid reshapes MUST compile =="
check "Functor ZipList override"     accept "data P a = P [a] deriving Functor                  via Overriding1 P '[ '[ZipList] ]"
check "Category sparse At (Basic/Kleisli)" accept "data T3 a b = T3 { zero :: String, one :: a -> b, two :: a -> [b] }
  deriving Category via Overriding2 T3 '[ T3 at 0 via Basic String, T3 at 2 via Kleisli [] ]"
check "Category b->a via Op (->)"    accept "data T4 a b = T4 { g :: b -> a } deriving Category      via Overriding2 T4 '[ T4 at 0 via Op (->) ]"
# a value-polymorphic Stock2 modifier (cat free in Op cat): fixMod2Kind preserves
# the genuine value variable instead of defaulting it to Type.
check "Stock2 value-poly modifier Op cat" accept "data Tr cat a b = Tr (cat b a)
deriving via Overriding2 (Tr cat) '[ '[ Op cat ] ] instance Category cat => Category (Tr cat)"
# A data/type-family-instance field (e.g. cardano-crypto's VerificationKey) has a
# representation tycon that crashes Core codegen; we refuse it cleanly (a clean
# error, not a GHC panic).  Same root as UNPACK; full support is roadmap.
check "data-family field rejected" reject "data family VKF a
newtype instance VKF Int = VKF Char
deriving instance Show (VKF Int)
data W = W (VKF Int) deriving Show via Stock W"

echo
if [ "$fails" -eq 0 ]; then echo "negative harness: all expectations met"; else echo "negative harness: $fails FAILURE(S)"; fi
exit "$fails"
