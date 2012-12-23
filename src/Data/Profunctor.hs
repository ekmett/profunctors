-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Profunctor
-- Copyright   :  (C) 2011-2012 Edward Kmett,
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
-- For a good explanation of profunctors in Haskell see Dan Piponi's article:
--
-- <http://blog.sigfpe.com/2011/07/profunctors-in-haskell.html>
----------------------------------------------------------------------------
module Data.Profunctor
  ( Profunctor(..)
  , UpStar(..)
  , DownStar(..)
  , WrappedArrow(..)
  , Prismatic(..)
  , Lenticular(..)
  ) where

import Control.Applicative hiding (WrappedArrow(..))
import Control.Arrow
import Control.Category
import Control.Comonad (Cokleisli(..))
import Control.Monad (liftM)
import Data.Tagged
import Data.Traversable
import Prelude hiding (id,(.),sequence)
----------------------------------------------------------------------------
-- Profunctors
----------------------------------------------------------------------------

-- | Formally, 'Profunctor' represents a 'profunctor' from @Hask@ -> @Hask@
--
-- Intuitively it is a bifunctor where the first argument is contravariant
-- and the second argument is covariant.
--
-- You can define a profunctor by either defining 'dimap' or by defining both
-- 'lmap' and 'rmap'.
--
-- If you supply 'dimap', you should ensure that:
--
-- @'dimap' 'id' 'id' ≡ 'id'@
--
-- If you supply 'lmap' and 'rmap', ensure:
--
-- @
-- 'lmap' 'id' ≡ 'id'
-- 'rmap' 'id' ≡ 'id'
-- @
--
-- If you supply both, you should also ensure:
--
-- @'dimap' f g ≡ 'lmap' f . 'rmap' g@
--
-- These ensure by parametricity:
--
-- @
-- 'dimap' (f . g) (h . i) ≡ 'dimap' g h '.' 'dimap' f i
-- 'lmap' (f . g) ≡ 'lmap' g '.' 'lmap' f
-- 'rmap' (f . g) ≡ 'rmap' f '.' 'rmap' g
-- @
class Profunctor p where
  -- | Map over both arguments at the same time.
  --
  -- @'dimap' f g ≡ 'lmap' f '.' 'rmap' g@
  dimap :: (a -> b) -> (c -> d) -> p b c -> p a d
  dimap f g = lmap f . rmap g
  {-# INLINE dimap #-}

  -- | Map the first argument contravariantly
  --
  -- @'lmap' f ≡ 'dimap' f 'id'@
  lmap :: (a -> b) -> p b c -> p a c
  lmap f = dimap f id
  {-# INLINE lmap #-}

  -- | Map the second argument covariantly
  --
  -- @'rmap' ≡ 'dimap' 'id'@
  rmap :: (b -> c) -> p a b -> p a c
  rmap = dimap id
  {-# INLINE rmap #-}

instance Profunctor (->) where
  dimap ab cd bc = cd . bc . ab
  {-# INLINE dimap #-}
  lmap = flip (.)
  {-# INLINE lmap #-}
  rmap = (.)
  {-# INLINE rmap #-}

instance Profunctor Tagged where
  dimap _ f (Tagged s) = Tagged (f s)
  {-# INLINE dimap #-}
  lmap _ = retag
  {-# INLINE lmap #-}
  rmap = fmap
  {-# INLINE rmap #-}

instance Monad m => Profunctor (Kleisli m) where
  dimap f g (Kleisli h) = Kleisli (liftM g . h . f)
  {-# INLINE dimap #-}
  lmap k (Kleisli f) = Kleisli (f . k)
  {-# INLINE lmap #-}
  rmap k (Kleisli f) = Kleisli (liftM k . f)
  {-# INLINE rmap #-}

instance Functor w => Profunctor (Cokleisli w) where
  dimap f g (Cokleisli h) = Cokleisli (g . h . fmap f)
  {-# INLINE dimap #-}
  lmap k (Cokleisli f) = Cokleisli (f . fmap k)
  {-# INLINE lmap #-}
  rmap k (Cokleisli f) = Cokleisli (k . f)
  {-# INLINE rmap #-}

------------------------------------------------------------------------------
-- UpStar
------------------------------------------------------------------------------

-- | Lift a 'Functor' into a 'Profunctor' (forwards)
newtype UpStar f d c = UpStar { runUpStar :: d -> f c }

instance Functor f => Profunctor (UpStar f) where
  dimap ab cd (UpStar bfc) = UpStar (fmap cd . bfc . ab)
  {-# INLINE dimap #-}
  lmap k (UpStar f) = UpStar (f . k)
  {-# INLINE lmap #-}
  rmap k (UpStar f) = UpStar (fmap k . f)
  {-# INLINE rmap #-}

instance Functor f => Functor (UpStar f a) where
  fmap = rmap
  {-# INLINE fmap #-}

------------------------------------------------------------------------------
-- DownStar
------------------------------------------------------------------------------

-- | Lift a 'Functor' into a 'Profunctor' (backwards)
newtype DownStar f d c = DownStar { runDownStar :: f d -> c }

instance Functor f => Profunctor (DownStar f) where
  dimap ab cd (DownStar fbc) = DownStar (cd . fbc . fmap ab)
  {-# INLINE dimap #-}
  lmap k (DownStar f) = DownStar (f . fmap k)
  {-# INLINE lmap #-}
  rmap k (DownStar f) = DownStar (k . f)
  {-# INLINE rmap #-}

instance Functor (DownStar f a) where
  fmap k (DownStar f) = DownStar (k . f)
  {-# INLINE fmap #-}

------------------------------------------------------------------------------
-- Wrapped Profunctors
------------------------------------------------------------------------------

-- | Wrap an arrow for use as a 'Profunctor'
newtype WrappedArrow p a b = WrapArrow { unwrapArrow :: p a b }

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

------------------------------------------------------------------------------
-- Prismatic
------------------------------------------------------------------------------

-- | Generalization of downstar of a costrong functor
class Profunctor p => Prismatic p where
  prismatic :: p a b -> p (Either b a) b

instance Prismatic (->) where
  prismatic = either id

instance Monad m => Prismatic (Kleisli m) where
  prismatic (Kleisli pab) = Kleisli (either return pab)

-- | 'sequence' approximates 'costrength'
instance Traversable w => Prismatic (Cokleisli w) where
  prismatic (Cokleisli wab) = Cokleisli (either id wab . sequence)

-- | 'sequence' approximates 'costrength'
instance Traversable w => Prismatic (DownStar w) where
  prismatic (DownStar wab) = DownStar (either id wab . sequence)

------------------------------------------------------------------------------
-- Lenticular
------------------------------------------------------------------------------

-- | Generalizing upstar of a strong 'Functor'
class Profunctor p => Lenticular p where
  lenticular :: p a b -> p a (a, b)

instance Lenticular (->) where
  lenticular f a = (a, f a)

instance Monad m => Lenticular (Kleisli m) where
  lenticular (Kleisli f) = Kleisli $ \ a -> do
     b <- f a
     return (a, b)

-- | Every 'Functor' in Haskell is strong.
instance Functor m => Lenticular (UpStar m) where
  lenticular (UpStar f) = UpStar $ \ a -> (,) a <$> f a
