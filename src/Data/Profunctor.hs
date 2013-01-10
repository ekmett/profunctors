{-# LANGUAGE CPP #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif
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
--
-- For more information on strength and costrength, see:
--
-- <http://comonad.com/reader/2008/deriving-strength-from-laziness/>
----------------------------------------------------------------------------
module Data.Profunctor
  (
  -- * Profunctors
    Profunctor(dimap,lmap,rmap)
  -- ** Profunctorial Strength
  , Lenticular(..)
  , Prismatic(..)
  -- ** Common Profunctors
  , UpStar(..)
  , DownStar(..)
  , WrappedArrow(..)
  ) where

import Control.Applicative hiding (WrappedArrow(..))
import Control.Arrow
import Control.Category
import Control.Comonad (Cokleisli(..))
import Data.Tagged
import Data.Traversable
import Data.Profunctor.Unsafe
import Prelude hiding (id,(.),sequence)
import Unsafe.Coerce

------------------------------------------------------------------------------
-- UpStar
------------------------------------------------------------------------------

-- | Lift a 'Functor' into a 'Profunctor' (forwards).
newtype UpStar f d c = UpStar { runUpStar :: d -> f c }

instance Functor f => Profunctor (UpStar f) where
  dimap ab cd (UpStar bfc) = UpStar (fmap cd . bfc . ab)
  {-# INLINE dimap #-}
  lmap k (UpStar f) = UpStar (f . k)
  {-# INLINE lmap #-}
  rmap k (UpStar f) = UpStar (fmap k . f)
  {-# INLINE rmap #-}
  -- We cannot safely overload ( #. ) because we didn't write the 'Functor'.
  p .# _ = unsafeCoerce p
  {-# INLINE ( .# ) #-}

instance Functor f => Functor (UpStar f a) where
  fmap = rmap
  {-# INLINE fmap #-}

------------------------------------------------------------------------------
-- DownStar
------------------------------------------------------------------------------

-- | Lift a 'Functor' into a 'Profunctor' (backwards).
newtype DownStar f d c = DownStar { runDownStar :: f d -> c }

instance Functor f => Profunctor (DownStar f) where
  dimap ab cd (DownStar fbc) = DownStar (cd . fbc . fmap ab)
  {-# INLINE dimap #-}
  lmap k (DownStar f) = DownStar (f . fmap k)
  {-# INLINE lmap #-}
  rmap k (DownStar f) = DownStar (k . f)
  {-# INLINE rmap #-}
  ( #. ) _ = unsafeCoerce
  {-# INLINE ( #. ) #-}
  -- We cannot overload ( .# ) because we didn't write the 'Functor'.

instance Functor (DownStar f a) where
  fmap k (DownStar f) = DownStar (k . f)
  {-# INLINE fmap #-}

------------------------------------------------------------------------------
-- Wrapped Profunctors
------------------------------------------------------------------------------

-- | Wrap an arrow for use as a 'Profunctor'.
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
  -- We cannot safely overload ( #. ) or ( .# ) because we didn't write the 'Arrow'.

------------------------------------------------------------------------------
-- Lenticular
------------------------------------------------------------------------------

-- | Generalizing upstar of a strong 'Functor'
--
-- /Note:/ Every 'Functor' in Haskell is strong.
class Profunctor p => Lenticular p where
  lenticular :: p a b -> p a (a, b)

instance Lenticular (->) where
  lenticular f a = (a, f a)
  {-# INLINE lenticular #-}

instance Monad m => Lenticular (Kleisli m) where
  lenticular (Kleisli f) = Kleisli $ \ a -> do
     b <- f a
     return (a, b)
  {-# INLINE lenticular #-}

instance Functor m => Lenticular (UpStar m) where
  lenticular (UpStar f) = UpStar $ \ a -> (,) a <$> f a
  {-# INLINE lenticular #-}

instance Arrow p => Lenticular (WrappedArrow p) where
  lenticular (WrapArrow k) = WrapArrow (id &&& k)
  {-# INLINE lenticular #-}

------------------------------------------------------------------------------
-- Prismatic
------------------------------------------------------------------------------

-- | The generalization of 'DownStar' of a \"Costrong\" 'Functor'.
--
-- /Note:/ Here we use 'Traversable' as an approximate costrength.
class Profunctor p => Prismatic p where
  prismatic :: p a b -> p (Either b a) b

instance Prismatic (->) where
  prismatic = either id
  {-# INLINE prismatic #-}

instance Monad m => Prismatic (Kleisli m) where
  prismatic (Kleisli pab) = Kleisli (either return pab)
  {-# INLINE prismatic #-}

-- | 'sequence' approximates 'costrength'.
instance Traversable w => Prismatic (Cokleisli w) where
  prismatic (Cokleisli wab) = Cokleisli (either id wab . sequence)
  {-# INLINE prismatic #-}

-- | 'sequence' approximates 'costrength'.
instance Traversable w => Prismatic (DownStar w) where
  prismatic (DownStar wab) = DownStar (either id wab . sequence)
  {-# INLINE prismatic #-}

instance Prismatic Tagged where
  prismatic = retag
  {-# INLINE prismatic #-}

instance ArrowChoice p => Prismatic (WrappedArrow p) where
  prismatic (WrapArrow k) = WrapArrow (id ||| k)
  {-# INLINE prismatic #-}
