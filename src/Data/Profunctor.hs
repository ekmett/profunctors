{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
  -- ** Profunctorial Costrength
  , Costrong(..)
  , Cochoice(..)
  -- ** Common Profunctors
  , Star(..)
  , Costar(..)
  , WrappedArrow(..)
  , Forget(..)
#ifndef HLINT
  , (:->)
#endif
  ) where

import Control.Applicative hiding (WrappedArrow(..))
import Control.Arrow
import Control.Category
import Control.Comonad
import Control.Monad (liftM, MonadPlus(..))
import Control.Monad.Fix
import Data.Distributive
import Data.Foldable
import Data.Monoid
import Data.Tagged
import Data.Traversable
import Data.Tuple
import Data.Profunctor.Unsafe
import Prelude hiding (id,(.),sequence)

#if __GLASGOW_HASKELL__ >= 708
import Data.Coerce
#else
import Unsafe.Coerce
#endif

infixr 0 :->
type p :-> q = forall a b. p a b -> q a b

------------------------------------------------------------------------------
-- Star
------------------------------------------------------------------------------

-- | Lift a 'Functor' into a 'Profunctor' (forwards).
newtype Star f d c = Star { runStar :: d -> f c }

instance Functor f => Profunctor (Star f) where
  dimap ab cd (Star bfc) = Star (fmap cd . bfc . ab)
  {-# INLINE dimap #-}
  lmap k (Star f) = Star (f . k)
  {-# INLINE lmap #-}
  rmap k (Star f) = Star (fmap k . f)
  {-# INLINE rmap #-}
  -- We cannot safely overload ( #. ) because we didn't write the 'Functor'.
#if __GLASGOW_HASKELL__ >= 708
  p .# _ = coerce p
#else
  p .# _ = unsafeCoerce p
#endif
  {-# INLINE ( .# ) #-}

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
  return a = Star $ \_ -> return a
  Star m >>= f = Star $ \ e -> do
    a <- m e
    runStar (f a) e

instance MonadPlus f => MonadPlus (Star f a) where
  mzero = Star $ \_ -> mzero
  Star f `mplus` Star g = Star $ \a -> f a `mplus` g a

instance Distributive f => Distributive (Star f a) where
  distribute fs = Star $ \a -> collect (($ a) .# runStar) fs

------------------------------------------------------------------------------
-- Costar
------------------------------------------------------------------------------

-- | Lift a 'Functor' into a 'Profunctor' (backwards).
newtype Costar f d c = Costar { runCostar :: f d -> c }

instance Functor f => Profunctor (Costar f) where
  dimap ab cd (Costar fbc) = Costar (cd . fbc . fmap ab)
  {-# INLINE dimap #-}
  lmap k (Costar f) = Costar (f . fmap k)
  {-# INLINE lmap #-}
  rmap k (Costar f) = Costar (k . f)
  {-# INLINE rmap #-}
#if __GLASGOW_HASKELL__ >= 708
  ( #. ) _ = coerce (\x -> x :: b) :: forall a b. Coercible b a => a -> b
#else
  ( #. ) _ = unsafeCoerce
#endif
  {-# INLINE ( #. ) #-}
  -- We cannot overload ( .# ) because we didn't write the 'Functor'.

instance Distributive (Costar f d) where
  distribute fs = Costar $ \gd -> fmap (($ gd) .# runCostar) fs

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
  return a = Costar $ \_ -> a
  Costar m >>= f = Costar $ \ x -> runCostar (f (m x)) x

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

-- | Generalizing 'Star' of a strong 'Functor'
--
-- /Note:/ Every 'Functor' in Haskell is strong with respect to @(,)@.
--
-- This describes profunctor strength with respect to the product structure
-- of Hask.
--
-- <http://www-kb.is.s.u-tokyo.ac.jp/~asada/papers/arrStrMnd.pdf>
class Profunctor p => Strong p where
  first' :: p a b  -> p (a, c) (b, c)
  first' = dimap swap swap . second'

  second' :: p a b -> p (c, a) (c, b)
  second' = dimap swap swap . first'


#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 708
  {-# MINIMAL first' | second' #-}
#endif

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

instance Functor m => Strong (Star m) where
  first' (Star f) = Star $ \ ~(a, c) -> (\b' -> (b', c)) <$> f a
  {-# INLINE first' #-}
  second' (Star f) = Star $ \ ~(c, a) -> (,) c <$> f a
  {-# INLINE second' #-}

-- | 'Arrow' is 'Strong' 'Category'
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

-- | The generalization of 'Costar' of 'Functor' that is strong with respect
-- to 'Either'.
--
-- Note: This is also a notion of strength, except with regards to another monoidal
-- structure that we can choose to equip Hask with: the cocartesian coproduct.
class Profunctor p => Choice p where
  left'  :: p a b -> p (Either a c) (Either b c)
  left' =  dimap (either Right Left) (either Right Left) . right'

  right' :: p a b -> p (Either c a) (Either c b)
  right' =  dimap (either Right Left) (either Right Left) . left'

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 708
  {-# MINIMAL left' | right' #-}
#endif

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

instance Applicative f => Choice (Star f) where
  left' (Star f) = Star $ either (fmap Left . f) (fmap Right . pure)
  {-# INLINE left' #-}
  right' (Star f) = Star $ either (fmap Left . pure) (fmap Right . f)
  {-# INLINE right' #-}

-- | 'extract' approximates 'costrength'
instance Comonad w => Choice (Cokleisli w) where
  left' = left
  {-# INLINE left' #-}
  right' = right
  {-# INLINE right' #-}

-- NB: This instance is highly questionable
instance Traversable w => Choice (Costar w) where
  left' (Costar wab) = Costar (either Right Left . fmap wab . traverse (either Right Left))
  {-# INLINE left' #-}
  right' (Costar wab) = Costar (fmap wab . sequence)
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

--------------------------------------------------------------------------------
-- * Costrength for (,)
--------------------------------------------------------------------------------

-- | Analogous to 'ArrowLoop', 'loop' = 'unfirst'
class Profunctor p => Costrong p where
  unfirst  :: p (a, d) (b, d) -> p a b
  unfirst = unsecond . dimap swap swap

  unsecond :: p (d, a) (d, b) -> p a b
  unsecond = unfirst . dimap swap swap

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 708
  {-# MINIMAL unfirst | unsecond #-}
#endif

instance Costrong (->) where
  unfirst f a = b where (b, d) = f (a, d)
  unsecond f a = b where (d, b) = f (d, a)

instance Costrong Tagged where
  unfirst (Tagged bd) = Tagged (fst bd)
  unsecond (Tagged db) = Tagged (snd db)

instance ArrowLoop p => Costrong (WrappedArrow p) where
  unfirst (WrapArrow k) = WrapArrow (loop k)

instance MonadFix m => Costrong (Kleisli m) where
  unfirst (Kleisli f) = Kleisli (liftM fst . mfix . f')
    where f' x y = f (x, snd y)

--------------------------------------------------------------------------------
-- * Costrength for Either
--------------------------------------------------------------------------------

class Profunctor p => Cochoice p where
  unleft  :: p (Either a d) (Either b d) -> p a b
  unleft = unright . dimap (either Right Left) (either Right Left)

  unright :: p (Either d a) (Either d b) -> p a b
  unright = unleft . dimap (either Right Left) (either Right Left)

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 708
  {-# MINIMAL unleft | unright #-}
#endif
