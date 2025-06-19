{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Trustworthy #-}

-- |
-- Copyright   :  (C) 2011-2015 Edward Kmett,
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
-- For a good explanation of profunctors in Haskell see Dan Piponi's article:
--
-- <https://github.com/dpiponi/StableBlog/blob/main/Profunctors/Profunctors.pdf>
--
-- For more information on strength and costrength, see:
--
-- <http://comonad.com/reader/2008/deriving-strength-from-laziness/>

module Data.Profunctor.Types
( Profunctor(dimap, lmap, rmap)
, Star(..)
, Costar(..)
, WrappedArrow(..)
, Forget(..)
, (:->)
) where

import Control.Applicative hiding (WrappedArrow(..))
import Control.Arrow
import Control.Category
import Control.Comonad
import Control.Monad (MonadPlus(..), (>=>))
import Control.Monad.Fix
import Data.Bifunctor.Functor ((:->))
import Data.Coerce (Coercible, coerce)
import Data.Foldable
import Data.Functor.Contravariant
import Data.Profunctor.Unsafe
import Data.Traversable
import GHC.Generics
import Prelude hiding (id,(.))

------------------------------------------------------------------------------
-- Star
------------------------------------------------------------------------------

-- | Lift a 'Functor' into a 'Profunctor' (forwards).
--
-- 'Star' has a polymorphic kind since @5.6@.

-- Star :: (k -> Type) -> (Type -> k -> Type)
newtype Star f d c = Star { runStar :: d -> f c }
  deriving (Generic, Generic1)

instance Functor f => Profunctor (Star f) where
  dimap ab cd (Star bfc) = Star (fmap cd . bfc . ab)
  {-# INLINE dimap #-}
  lmap k (Star f) = Star (f . k)
  {-# INLINE lmap #-}
  rmap k (Star f) = Star (fmap k . f)
  {-# INLINE rmap #-}
  -- We cannot safely overload (#.) because we didn't write the 'Functor'.
  p .# _ = coerce p
  {-# INLINE (.#) #-}

instance Functor f => Functor (Star f a) where
  fmap = rmap
  {-# INLINE fmap #-}

instance Applicative f => Applicative (Star f a) where
  pure a = Star $ \_ -> pure a
  Star ff <*> Star fx = Star $ \a -> ff a <*> fx a
  Star ff  *> Star fx = Star $ \a -> ff a  *> fx a
  Star ff <*  Star fx = Star $ \a -> ff a <*  fx a

instance Alternative f => Alternative (Star f a) where
  empty = Star $ \_ -> empty
  Star f <|> Star g = Star $ \a -> f a <|> g a

instance Monad f => Monad (Star f a) where
  Star m >>= f = Star $ \ e -> do
    a <- m e
    runStar (f a) e

instance MonadPlus f => MonadPlus (Star f a) where
  mzero = Star $ \_ -> mzero
  Star f `mplus` Star g = Star $ \a -> f a `mplus` g a

instance Monad f => Category (Star f) where
  id = Star return
  Star f . Star g = Star $ g >=> f

instance Monad f => Arrow (Star f) where
  arr f = Star (pure . f)
  {-# INLINE arr #-}
  first (Star f) = Star $ \ ~(a, c) -> (\b' -> (b', c)) <$> f a
  {-# INLINE first #-}
  second (Star f) = Star $ \ ~(c, a) -> (,) c <$> f a
  {-# INLINE second #-}
  Star f *** Star g = Star $ \ ~(x, y) -> liftA2 (flip (,)) (g y) (f x)
  {-# INLINE (***) #-}
  Star f &&& Star g = Star $ \ x -> liftA2 (flip (,)) (g x) (f x)
  {-# INLINE (&&&) #-}

instance MonadPlus f => ArrowZero (Star f) where
  zeroArrow = Star $ \_ -> mzero
  {-# INLINE zeroArrow #-}

instance MonadPlus f => ArrowPlus (Star f) where
  Star f <+> Star g = Star $ \x -> mplus (f x) (g x)
  {-# INLINE (<+>) #-}

instance Monad f => ArrowChoice (Star f) where
  left (Star f) = Star $ either (fmap Left . f) (pure . Right)
  {-# INLINE left #-}
  right (Star f) = Star $ either (pure . Left) (fmap Right . f)
  {-# INLINE right #-}

instance Monad f => ArrowApply (Star f) where
  app = Star $ \ ~(Star f, x) -> f x
  {-# INLINE app #-}

instance MonadFix f => ArrowLoop (Star f) where
  loop (Star f) = Star $ \x -> fst <$> mfix (\ ~(_, y) -> f (x, y))
  {-# INLINE loop #-}

instance Contravariant f => Contravariant (Star f a) where
  contramap f (Star g) = Star (contramap f . g)
  {-# INLINE contramap #-}

------------------------------------------------------------------------------
-- Costar
------------------------------------------------------------------------------

-- | Lift a 'Functor' into a 'Profunctor' (backwards).
--
-- 'Costar' has a polymorphic kind since @5.6@.

-- Costar :: (k -> Type) -> k -> Type -> Type
newtype Costar f d c = Costar { runCostar :: f d -> c }
  deriving (Generic, Generic1)

instance Functor f => Profunctor (Costar f) where
  dimap ab cd (Costar fbc) = Costar (cd . fbc . fmap ab)
  {-# INLINE dimap #-}
  lmap k (Costar f) = Costar (f . fmap k)
  {-# INLINE lmap #-}
  rmap k (Costar f) = Costar (k . f)
  {-# INLINE rmap #-}
  (#.) _ = coerce (\x -> x :: b) :: forall a b. Coercible b a => a -> b
  {-# INLINE (#.) #-}
  -- We cannot overload (.#) because we didn't write the 'Functor'.

instance Functor (Costar f a) where
  fmap k (Costar f) = Costar (k . f)
  {-# INLINE fmap #-}
  a <$ _ = Costar $ \_ -> a
  {-# INLINE (<$) #-}

instance Applicative (Costar f a) where
  pure a = Costar $ \_ -> a
  Costar ff <*> Costar fx = Costar $ \a -> ff a (fx a)
  _ *> m = m
  m <* _ = m

instance Monad (Costar f a) where
  return = pure
  Costar m >>= f = Costar $ \ x -> runCostar (f (m x)) x

instance Comonad f => Category (Costar f) where
  id = Costar extract
  {-# INLINE id #-}
  Costar f . Costar g = Costar (f =<= g)
  {-# INLINE (.) #-}

------------------------------------------------------------------------------
-- Wrapped Profunctors
------------------------------------------------------------------------------

-- | This newtype allows 'Profunctor' classes to be used with types that only
-- implement @base@'s arrow classes.
--
-- - 'Arrow' is equivalent to 'Category'
--   && t'Data.Profunctor.Strong.Strong'.
-- - 'ArrowChoice' is equivalent to 'Category'
--   && t'Data.Profunctor.Strong.Strong' && t'Data.Profunctor.Choice.Choice'.
-- - 'ArrowLoop' is equivalent to 'Category'
--   && t'Data.Profunctor.Strong.Strong' && t'Data.Profunctor.Strong.Costrong'.
--
-- 'WrappedArrow' has a polymorphic kind since @5.6@.

-- WrappedArrow :: (k1 -> k2 -> Type) -> (k1 -> k2 -> Type)
newtype WrappedArrow p a b = WrapArrow { unwrapArrow :: p a b }

instance Arrow p => Functor (WrappedArrow p a) where
  fmap f p = arr f . p
  {-# INLINE fmap #-}

instance Category p => Category (WrappedArrow p) where
  WrapArrow f . WrapArrow g = WrapArrow (f . g)
  {-# INLINE (.) #-}
  id = WrapArrow id
  {-# INLINE id #-}

instance Arrow p => Arrow (WrappedArrow p) where
  arr = WrapArrow . arr
  {-# INLINE arr #-}
  first = WrapArrow . first . unwrapArrow
  {-# INLINE first #-}
  second = WrapArrow . second . unwrapArrow
  {-# INLINE second #-}
  WrapArrow a *** WrapArrow b = WrapArrow (a *** b)
  {-# INLINE (***) #-}
  WrapArrow a &&& WrapArrow b = WrapArrow (a &&& b)
  {-# INLINE (&&&) #-}

instance ArrowZero p => ArrowZero (WrappedArrow p) where
  zeroArrow = WrapArrow zeroArrow
  {-# INLINE zeroArrow #-}

instance ArrowPlus p => ArrowPlus (WrappedArrow p) where
  WrapArrow p <+> WrapArrow q = WrapArrow (p <+> q)
  {-# INLINE (<+>) #-}

instance ArrowChoice p => ArrowChoice (WrappedArrow p) where
  left = WrapArrow . left . unwrapArrow
  {-# INLINE left #-}
  right = WrapArrow . right . unwrapArrow
  {-# INLINE right #-}
  WrapArrow a +++ WrapArrow b = WrapArrow (a +++ b)
  {-# INLINE (+++) #-}
  WrapArrow a ||| WrapArrow b = WrapArrow (a ||| b)
  {-# INLINE (|||) #-}

instance ArrowApply p => ArrowApply (WrappedArrow p) where
  app = WrapArrow $ app . arr (first unwrapArrow)
  {-# INLINE app #-}

instance ArrowLoop p => ArrowLoop (WrappedArrow p) where
  loop = WrapArrow . loop . unwrapArrow
  {-# INLINE loop #-}

instance Arrow p => Profunctor (WrappedArrow p) where
  lmap = (^>>)
  {-# INLINE lmap #-}
  rmap = (^<<)
  {-# INLINE rmap #-}
  -- We cannot safely overload (#.) or (.#) because we didn't write the 'Arrow'.

------------------------------------------------------------------------------
-- Forget
------------------------------------------------------------------------------

-- | 'Forget' has a polymorphic kind since @5.6@.

-- Forget :: Type -> Type -> k -> Type
newtype Forget r a b = Forget { runForget :: a -> r }

instance Profunctor (Forget r) where
  dimap f _ (Forget k) = Forget (k . f)
  {-# INLINE dimap #-}
  lmap f (Forget k) = Forget (k . f)
  {-# INLINE lmap #-}
  rmap _ (Forget k) = Forget k
  {-# INLINE rmap #-}

instance Functor (Forget r a) where
  fmap _ (Forget k) = Forget k
  {-# INLINE fmap #-}

instance Foldable (Forget r a) where
  foldMap _ _ = mempty
  {-# INLINE foldMap #-}

instance Traversable (Forget r a) where
  traverse _ (Forget k) = pure (Forget k)
  {-# INLINE traverse #-}

instance Contravariant (Forget r a) where
  contramap _ (Forget k) = Forget k
  {-# INLINE contramap #-}

-- | Via @Semigroup r => (a -> r)@
--
-- @since 5.6.2
instance Semigroup r => Semigroup (Forget r a b) where
  Forget f <> Forget g = Forget (f <> g)
  {-# INLINE (<>) #-}

-- | Via @Monoid r => (a -> r)@
--
-- @since 5.6.2
instance Monoid r => Monoid (Forget r a b) where
  mempty = Forget mempty
  {-# INLINE mempty #-}

-- | Via @Monoid r => (a -> r)@
--
-- >>> let printer = (,) <$> fst `lmap` Forget id <*> snd `lmap` Forget show
-- >>> runForget printer ("string",True)
-- "stringTrue"
instance Monoid r => Applicative (Forget r a) where
  pure _ = Forget mempty
  {-# INLINE pure #-}
  Forget f <*> Forget g = Forget (f <> g)
  {-# INLINE (<*>) #-}
