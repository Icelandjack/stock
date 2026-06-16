{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}

-- | Newtype wrappers that drive the Stock plugin.  Writing
-- @deriving C via Stock T@ (or @via Stock1 F@ for a class over a type
-- constructor) asks the plugin to synthesize the instance from @T@'s
-- structure — no @Generic@, no hand-written instances.
module Stock.Type
  ( Stock(Stock, unStock)
  , Stock1(Stock1, unStock1)
  , Stock2(Stock2, unStock2)
  ) where

import Data.Kind (Type)

-- | Wrap a type @a@ so that @deriving C via Stock a@ synthesizes @C a@.
type    Stock :: Type -> Type
newtype Stock a = Stock { unStock :: a }

-- | Wrap a type constructor @f@ so that @deriving C via Stock1 f@ synthesizes
-- a @C f@ instance (for classes over type constructors, e.g. @Functor@).
-- Poly-kinded in the index (@f :: k -> Type@) so it works for classes over
-- non-@Type@ indices too (e.g. @TestEquality@) — maximally polymorphic.
type    Stock1 :: forall k. (k -> Type) -> (k -> Type)
newtype Stock1 f a = Stock1 { unStock1 :: f a }

-- | Wrap a two-parameter type constructor @p@ so that @deriving C via Stock2 p@
-- synthesizes a @C p@ instance (for classes over two-parameter type
-- constructors, e.g. @Bifunctor@, @Bifoldable@, @Eq2@, @Ord2@, @Show2@,
-- @Read2@, @Category@).
type    Stock2 :: forall k j. (k -> j -> Type) -> (k -> j -> Type)
newtype Stock2 bi a b = Stock2 { unStock2 :: bi a b }
