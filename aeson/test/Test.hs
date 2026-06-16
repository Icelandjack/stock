{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE UndecidableInstances #-}   -- deriving Generic1 via Stock1 (Rep1 family)
{-# OPTIONS_GHC -fplugin Stock #-}
module Main (main) where

import Stock (Stock(..), Stock1(..), Stock2(..))
import Stock.Aeson  -- classes (incl. lifted) + registers all six DeriveStock(1,2) instances
  ( ToJSON(..), ToJSON1(..), ToJSON2(..), FromJSON(..), FromJSON1(..), FromJSON2(..) )
import Stock.Override (Override(..), Overriding1, Override1(..), Keep, type (:=))
import Data.Aeson
  ( Value, encode, decode, object, (.=)
  , genericToJSON, genericToEncoding, defaultOptions, fromJSON, Result(Success) )
import Data.Aeson.Types (GToJSON', Zero, toJSON1, toEncoding1, parseJSON1, parseMaybe
                        , toJSON2, toEncoding2, parseJSON2)
import Data.Aeson.Encoding (encodingToLazyByteString)
import GHC.Generics (Generic, Rep, Generic1)
import qualified Data.ByteString.Lazy.Char8 as BL
import Data.List (isInfixOf)
import Control.Monad (unless)
import System.Exit (exitFailure)

-- The whole point: stock-aeson must be a DROP-IN for aeson's own Generic
-- deriving (@deriving stock Generic@ + @deriving anyclass (ToJSON, FromJSON)@).
-- So for every shape we check, byte-for-byte (Value equality), that
--   * stock's  toJSON x  ==  aeson's  genericToJSON defaultOptions x
--   * stock's  parseJSON  accepts what  genericToJSON defaultOptions  produced.
-- Each type derives @stock Generic@ (the aeson reference) AND (ToJSON,FromJSON)
-- via Stock (the implementation under test).

-- nullary sum  -> bare strings "A0"/"A1"/"A2"
data Nul = N0 | N1 | N2 deriving (Eq, Show, Generic)
  deriving (ToJSON, FromJSON) via Stock Nul

-- sum: nullary, unary (bare contents), n-ary (array contents), record (keys)
data T = A | B Int | C Bool [Int] | R { rx :: Int, ry :: String }
  deriving (Eq, Show, Generic)
  deriving (ToJSON, FromJSON) via Stock T

-- single-constructor product (no tag) -> array
data Prod = Prod Int Bool deriving (Eq, Show, Generic)
  deriving (ToJSON, FromJSON) via Stock Prod

-- single-constructor record (no tag) -> object of keys
data RecS = RecS { sx :: Int, sy :: Bool } deriving (Eq, Show, Generic)
  deriving (ToJSON, FromJSON) via Stock RecS

-- single-constructor single-field (no tag) -> the bare value
data One = One Int deriving (Eq, Show, Generic)
  deriving (ToJSON, FromJSON) via Stock One

-- parameterised product
data P a = P a a Int deriving (Eq, Show, Generic)
  deriving (ToJSON, FromJSON) via Stock (P a)

-- | Drop-in: stock's encoding equals aeson's Generic encoding (byte-for-byte),
-- and stock's parser accepts aeson's Generic output.
dropIn :: (Eq a, ToJSON a, FromJSON a, Generic a, GToJSON' Value Zero (Rep a))
       => a -> Bool
dropIn x = toJSON x == ref && fromJSON ref == Success x
  where ref = genericToJSON defaultOptions x

roundtrips :: (ToJSON a, FromJSON a, Eq a) => a -> Bool
roundtrips x = decode (encode x) == Just x

-- value-level ToJSON/FromJSON via Override: @AsStr@ encodes an Int as a JSON
-- /string/ (and parses it back), so honouring the override is visible in the
-- bytes — the field is @"7"@, not the number @7@ — and it still round-trips.
newtype AsStr = AsStr Int deriving (Eq, Show)
instance ToJSON   AsStr where toJSON (AsStr n)  = toJSON (show n)
instance FromJSON AsStr where parseJSON v       = AsStr . read <$> parseJSON v
data JV = JV Int Bool
  deriving (Eq, Show)
  -- complex config: type-keyed (every @Int@ field via @AsStr@), not positional
  deriving (ToJSON, FromJSON) via Stock (Override JV '[ Int := AsStr ])

-- lifted ToJSON1/FromJSON1: stock supplies Generic1 (via Stock1) and aeson's
-- anyclass defaults (genericLiftToJSON / genericLiftParseJSON defaultOptions) do
-- the rest -- so it is byte-identical to a GHC-stock Generic1 twin.
data Lft  a = Lft a a [a] deriving (Eq, Show)
  deriving (ToJSON1, FromJSON1) via Stock1 Lft  -- BOTH via the stock-aeson satellite (under test)
data LftT a = LftT a a [a] deriving (Eq, Show)
  deriving stock Generic1
  deriving anyclass (ToJSON1, FromJSON1)        -- aeson's own generic deriving (the oracle)

-- lifted ToJSON2/FromJSON2 via Stock2.  aeson has no Generic2, so the oracle is
-- the VALUE generic on a same-shape twin (P2t): plugging @toJSON@ as both
-- per-parameter encoders must reproduce @genericToJSON defaultOptions@.
data P2  a b = P2 a b [b] deriving (Eq, Show)
  deriving (ToJSON2, FromJSON2) via Stock2 P2
data P2t a b = P2t a b [b] deriving (Eq, Show, Generic)

-- Override1 on a LIFTED JSON class (complex, field-keyed config): @items@'s list
-- is reshaped through RevJ, which reverses it in the wire form.  ToJSON1 and
-- FromJSON1 both honour it, so round-trips cancel and the reversal is observable.
newtype RevJ a = RevJ [a]
instance ToJSON1 RevJ where
  liftToJSON     o g gl (RevJ xs) = liftToJSON     o g gl (reverse xs)
  liftToEncoding o g gl (RevJ xs) = liftToEncoding o g gl (reverse xs)
instance FromJSON1 RevJ where
  liftParseJSON  o p pl v = RevJ . reverse <$> liftParseJSON o p pl v
data Boxed a = Boxed { items :: [a] } deriving (Eq, Show)
  deriving (ToJSON1, FromJSON1) via Overriding1 Boxed '[ items := RevJ ]

main :: IO ()
main = do
  let ok = and
        [ dropIn N1
        , dropIn A, dropIn (B 42), dropIn (C True [1, 2, 3])
        , dropIn (R { rx = 7, ry = "hi" })
        , dropIn (Prod 5 True)
        , dropIn (RecS { sx = 9, sy = False })
        , dropIn (One 99)
        , dropIn (P (1 :: Int) 2 3)
        , dropIn (P "x" "y" 9 :: P String)
          -- value Override: the Int field is encoded as the JSON string "7".
        , "\"7\"" `isInfixOf` BL.unpack (encode (JV 7 True))
        , roundtrips (JV 7 True)
          -- lifted ToJSON1 via Stock1 (the satellite deriver) == aeson's own
          -- generic deriving, byte-for-byte, on BOTH the Value and Encoding paths.
        , toJSON1 (Lft (1 :: Int) 2 [3, 4]) == toJSON1 (LftT (1 :: Int) 2 [3, 4])
        , encodingToLazyByteString (toEncoding1 (Lft (1 :: Int) 2 [3, 4]))
            == encodingToLazyByteString (toEncoding1 (LftT (1 :: Int) 2 [3, 4]))
        , parseMaybe parseJSON1 (toJSON1 (Lft (1 :: Int) 2 [3])) == Just (Lft 1 2 [3] :: Lft Int)
          -- cross-check: the satellite FromJSON1 accepts aeson's own generic output
        , parseMaybe parseJSON1 (toJSON1 (LftT (1 :: Int) 2 [3, 4])) == Just (Lft 1 2 [3, 4] :: Lft Int)
          -- lifted ToJSON2 via Stock2 (toJSON as both encoders) == value generic
        , toJSON2 (P2 (1 :: Int) True [False]) == genericToJSON defaultOptions (P2t (1 :: Int) True [False])
        , encodingToLazyByteString (toEncoding2 (P2 (1 :: Int) True [False]))
            == encodingToLazyByteString (genericToEncoding defaultOptions (P2t (1 :: Int) True [False]))
          -- FromJSON2 round-trips, and accepts the value-generic output
        , parseMaybe parseJSON2 (toJSON2 (P2 (1 :: Int) True [False])) == Just (P2 1 True [False] :: P2 Int Bool)
        , parseMaybe parseJSON2 (genericToJSON defaultOptions (P2t (1 :: Int) True [False])) == Just (P2 1 True [False] :: P2 Int Bool)
          -- Override1 on lifted ToJSON1/FromJSON1: round-trip cancels, and the
          -- wire form is observably reversed (parsing {items:[1,2,3]} -> Boxed [3,2,1]).
        , parseMaybe parseJSON1 (toJSON1 (Boxed [1, 2, 3 :: Int])) == Just (Boxed [1, 2, 3] :: Boxed Int)
        , parseMaybe parseJSON1 (object ["items" .= [1, 2, 3 :: Int]]) == Just (Boxed [3, 2, 1] :: Boxed Int)
        ]
  unless ok exitFailure
  putStrLn "ok: ToJSON/FromJSON is a drop-in for aeson Generic (defaultOptions) via stock-aeson"
