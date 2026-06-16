{-# OPTIONS_GHC -Wno-unused-top-binds #-}
-- | GHC-stock-derived twins with IDENTICAL constructor names, so the very same
-- input string can be fed to both the plugin's @Read@ and GHC's own derived
-- @Read@.  This is the oracle for the Read-parity checks in "Main".
module Twin where

import GHC.Generics (Generic)

-- mixed: nullary / prefix / record
data Sum = A | B Int | C Int Bool | Rec { rf :: Int, rg :: Bool }
  deriving (Eq, Show, Read)

-- infix with distinct fixities (must match the plugin-side type exactly)
infixr 5 :+:
infixl 6 :*:
data Expr = Lit Int | Expr :+: Expr | Expr :*: Expr
  deriving (Eq, Show, Read)

-- parameterised, for the Read1 oracle (instantiated at a concrete type)
data Trio a = Trio Int a [a]
  deriving (Eq, Show, Read)

-- parameterised record, for the Read1 record path
data Recd a = Recd { rx :: a, ry :: [a] }
  deriving (Eq, Show, Read)

-- parameterised INFIX, for the Read1 ambiguous-order oracle
infixr 5 :++
data InfF a = ILit a | InfF a :++ InfF a
  deriving (Eq, Show, Read)

-- two parameters, for the Read2 oracle
data Bi a b = Bi a b | OnlyA a | Bs b [b] | Tag Int
  deriving (Eq, Show, Read)

-- two-parameter INFIX (non-recursive: Read2's flat classifier can't take a
-- self-applied field), a sanity oracle for Read2's infix-constructor path
infixr 5 :**
data InfB a b = IB a b | a :** b
  deriving (Eq, Show, Read)

-- GHC-stock Generic twins (identical names/fixity/strictness), so the whole
-- Rep below D1 can be statically compared against the via-Stock version.
infixr 7 :*:.
data MOp  = Int :*:. Int   deriving (Eq, Show, Generic)
data MStr  = MStr  ![Int] Int deriving (Eq, Show, Generic)
data MSum = MN | MP Int Bool | MR { mrf :: Int, mrg :: Bool }
  deriving (Eq, Show, Generic)
