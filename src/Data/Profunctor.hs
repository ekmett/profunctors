{-# LANGUAGE CPP #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2011-2013 Edward Kmett,
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
  , Strong(..)
  , Choice(..)
  -- ** Common Profunctors
  , UpStar(..)
  , DownStar(..)
  , WrappedArrow(..)
  , Forget(..)
  ) where

import Control.Applicative hiding (WrappedArrow(..))
import Control.Arrow
import Control.Category
import Control.Comonad
import Data.Foldable
import Data.Monoid
import Data.Tagged
import Data.Traversable
import Data.Tuple
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
-- Forget
------------------------------------------------------------------------------

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

------------------------------------------------------------------------------
-- Strong
------------------------------------------------------------------------------

-- | Generalizing upstar of a strong 'Functor'
--
-- Minimal complete definition: 'first'' or 'second''
--
-- /Note:/ Every 'Functor' in Haskell is strong.
--
-- <http://takeichi.ipl-lab.org/~asada/papers/arrStrMnd.pdf>
class Profunctor p => Strong p where
  first' :: p a b  -> p (a, c) (b, c)
  first' = dimap swap swap . second'

  second' :: p a b -> p (c, a) (c, b)
  second' = dimap swap swap . first'

instance Strong (->) where
  first' ab ~(a, c) = (ab a, c)
  {-# INLINE first' #-}
  second' ab ~(c, a) = (c, ab a)

instance Monad m => Strong (Kleisli m) where
  first' (Kleisli f) = Kleisli $ \ ~(a, c) -> do
     b <- f a
     return (b, c)
  {-# INLINE first' #-}
  second' (Kleisli f) = Kleisli $ \ ~(c, a) -> do
     b <- f a
     return (c, b)
  {-# INLINE second' #-}

instance Functor m => Strong (UpStar m) where
  first' (UpStar f) = UpStar $ \ ~(a, c) -> (\b' -> (b', c)) <$> f a
  {-# INLINE first' #-}
  second' (UpStar f) = UpStar $ \ ~(c, a) -> (,) c <$> f a
  {-# INLINE second' #-}

-- | Every Arrow is a Strong Monad in Prof
instance Arrow p => Strong (WrappedArrow p) where
  first' (WrapArrow k) = WrapArrow (first k)
  {-# INLINE first' #-}
  second' (WrapArrow k) = WrapArrow (second k)
  {-# INLINE second' #-}

instance Strong (Forget r) where
  first' (Forget k) = Forget (k . fst)
  {-# INLINE first' #-}
  second' (Forget k) = Forget (k . snd)
  {-# INLINE second' #-}

------------------------------------------------------------------------------
-- Choice
------------------------------------------------------------------------------

-- | The generalization of 'DownStar' of a \"costrong\" 'Functor'
--
-- Minimal complete definition: 'left'' or 'right''
--
-- /Note:/ We use 'traverse' and 'extract' as approximate costrength as needed.
class Profunctor p => Choice p where
  left'  :: p a b -> p (Either a c) (Either b c)
  left' =  dimap (either Right Left) (either Right Left) . right'

  right' :: p a b -> p (Either c a) (Either c b)
  right' =  dimap (either Right Left) (either Right Left) . left'

instance Choice (->) where
  left' ab (Left a) = Left (ab a)
  left' _ (Right c) = Right c
  {-# INLINE left' #-}
  right' = fmap
  {-# INLINE right' #-}

instance Monad m => Choice (Kleisli m) where
  left' = left
  {-# INLINE left' #-}
  right' = right
  {-# INLINE right' #-}

instance Applicative f => Choice (UpStar f) where
  left' (UpStar f) = UpStar $ either (fmap Left . f) (fmap Right . pure)
  {-# INLINE left' #-}
  right' (UpStar f) = UpStar $ either (fmap Left . pure) (fmap Right . f)
  {-# INLINE right' #-}

-- | 'extract' approximates 'costrength'
instance Comonad w => Choice (Cokleisli w) where
  left' = left
  {-# INLINE left' #-}
  right' = right
  {-# INLINE right' #-}

-- | 'sequence' approximates 'costrength'
instance Traversable w => Choice (DownStar w) where
  left' (DownStar wab) = DownStar (either Right Left . fmap wab . traverse (either Right Left))
  {-# INLINE left' #-}
  right' (DownStar wab) = DownStar (fmap wab . sequence)
  {-# INLINE right' #-}

instance Choice Tagged where
  left' (Tagged b) = Tagged (Left b)
  {-# INLINE left' #-}
  right' (Tagged b) = Tagged (Right b)
  {-# INLINE right' #-}

instance ArrowChoice p => Choice (WrappedArrow p) where
  left' (WrapArrow k) = WrapArrow (left k)
  {-# INLINE left' #-}
  right' (WrapArrow k) = WrapArrow (right k)
  {-# INLINE right' #-}

instance Monoid r => Choice (Forget r) where
  left' (Forget k) = Forget (either k (const mempty))
  {-# INLINE left' #-}
  right' (Forget k) = Forget (either (const mempty) k)
  {-# INLINE right' #-}
