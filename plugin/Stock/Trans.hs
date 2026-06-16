{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE BlockArguments #-}
-- | A two-screen slice of @transformers@: the three monad transformers the
-- plugin uses (@ReaderT@, strict @WriterT@, @MaybeT@), inlined so the library
-- depends only on @base@ and @ghc@.  They are used /only/ as @DerivingVia@
-- targets (the synthesis monad in "Stock.Derive", the first-success 'Monoid' in
-- "Stock.Internal"), so the representations match @transformers@ exactly — that
-- is what lets the @via@ coercions go through — and none of the combinators
-- (@lift@, @ask@, @tell@, @runReaderT@, …) are needed beyond the constructors.
module Stock.Trans
  ( ReaderT(..)
  , WriterT(..)
  , MaybeT(..)
  ) where

import Control.Applicative (Alternative(..))
import Control.Monad (ap)
-- liftA2 comes from Prelude (base >= 4.18 / GHC >= 9.6)

-- | @r -> m a@, exactly as in @Control.Monad.Trans.Reader@.
newtype ReaderT r m a = ReaderT { runReaderT :: r -> m a }

-- | @m (a, w)@ — the /strict/ writer (value first), as in
-- @Control.Monad.Trans.Writer.Strict@.
newtype WriterT w m a = WriterT { runWriterT :: m (a, w) }

-- | @m (Maybe a)@, exactly as in @Control.Monad.Trans.Maybe@.
newtype MaybeT m a = MaybeT { runMaybeT :: m (Maybe a) }

instance Functor m => Functor (ReaderT r m) where
  fmap :: (a -> b) -> ReaderT r m a -> ReaderT r m b
  fmap f (ReaderT g) = ReaderT (fmap f . g)

instance Applicative m => Applicative (ReaderT r m) where
  pure :: a -> ReaderT r m a
  pure = ReaderT . const . pure
  (<*>) :: ReaderT r m (a -> b) -> ReaderT r m a -> ReaderT r m b
  ReaderT f <*> ReaderT x = ReaderT \r -> f r <*> x r

instance Monad m => Monad (ReaderT r m) where
  (>>=) :: ReaderT r m a -> (a -> ReaderT r m b) -> ReaderT r m b
  ReaderT x >>= k = ReaderT \r -> x r >>= \a -> runReaderT (k a) r

instance Functor m => Functor (WriterT w m) where
  fmap :: (a -> b) -> WriterT w m a -> WriterT w m b
  fmap f (WriterT m) = WriterT (fmap (\(a, w) -> (f a, w)) m)

instance (Monoid w, Applicative m) => Applicative (WriterT w m) where
  pure :: a -> WriterT w m a
  pure a = WriterT (pure (a, mempty))
  (<*>) :: WriterT w m (a -> b) -> WriterT w m a -> WriterT w m b
  WriterT mf <*> WriterT mx = WriterT (liftA2 k mf mx)
    where k (f, w) (x, w') = (f x, w <> w')

instance (Monoid w, Monad m) => Monad (WriterT w m) where
  (>>=) :: WriterT w m a -> (a -> WriterT w m b) -> WriterT w m b
  WriterT m >>= k = WriterT do
    (a, w)  <- m
    (b, w') <- runWriterT (k a)
    pure (b, w <> w')

instance Functor m => Functor (MaybeT m) where
  fmap :: (a -> b) -> MaybeT m a -> MaybeT m b
  fmap f (MaybeT m) = MaybeT (fmap (fmap f) m)

instance Monad m => Applicative (MaybeT m) where
  pure :: a -> MaybeT m a
  pure = MaybeT . pure . Just
  (<*>) :: MaybeT m (a -> b) -> MaybeT m a -> MaybeT m b
  (<*>) = ap

instance Monad m => Monad (MaybeT m) where
  (>>=) :: MaybeT m a -> (a -> MaybeT m b) -> MaybeT m b
  MaybeT m >>= k = MaybeT do
    ma <- m
    case ma of
      Nothing -> pure Nothing
      Just a  -> runMaybeT (k a)

instance Monad m => Alternative (MaybeT m) where
  empty :: MaybeT m a
  empty = MaybeT (pure Nothing)
  (<|>) :: MaybeT m a -> MaybeT m a -> MaybeT m a
  MaybeT a <|> MaybeT b = MaybeT do
    ma <- a
    case ma of
      Nothing -> b
      Just _  -> pure ma
