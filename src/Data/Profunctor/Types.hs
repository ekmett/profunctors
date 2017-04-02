{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

#if __GLASGOW_HASKELL__ >= 704 && __GLASGOW_HASKELL__ < 708
{-# LANGUAGE Trustworthy #-}
#endif

-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2011-2015 Edward Kmett,
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
module Data.Profunctor.Types
  ( Profunctor(dimap, lmap, rmap)
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
import Control.Monad (MonadPlus(..))
import Control.Monad.Fix
import Data.Distributive
import Data.Foldable
import Data.Monoid hiding (Product)
import Data.Profunctor.Unsafe
import Data.Traversable
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
#if __GLASGOW_HASKELL__ < 710
  return a = Star $ \_ -> return a
#endif
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
  return = pure
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

instance ArrowPlus p => ArrowPlus (WrappedArrow p) where
  WrapArrow a <+> WrapArrow b = WrapArrow (a <+> b)
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

instance Arrow p => Functor (WrappedArrow p r) where
  fmap = rmap
  {-# INLINE fmap #-}

instance Arrow p => Applicative (WrappedArrow p r) where
  pure = arr . const
  {-# INLINE pure #-}

  WrapArrow af <*> WrapArrow aa = WrapArrow $ arr (uncurry id) . (af &&& aa)
  {-# INLINE (<*>) #-}

  WrapArrow aa *> WrapArrow ab = WrapArrow $ arr snd . (aa &&& ab)
  {-# INLINE (*>) #-}

  WrapArrow aa <* WrapArrow ab = WrapArrow $ arr fst . (aa &&& ab)
  {-# INLINE (<*) #-}

instance ArrowPlus p => Alternative (WrappedArrow p r) where
  empty = zeroArrow
  {-# INLINE empty #-}

  (<|>) = (<+>)
  {-# INLINE (<|>) #-}

instance ArrowApply p => Monad (WrappedArrow p r) where
  return = pure
  {-# INLINE return #-}

  (>>) = (*>)
  {-# INLINE (>>) #-}

  WrapArrow p >>= f = WrapArrow $ app . (arr (unwrapArrow . f) . p &&& id)
  {-# INLINE (>>=) #-}

instance (ArrowApply p, ArrowPlus p) => MonadPlus (WrappedArrow p r) where
  mzero = zeroArrow
  {-# INLINE mzero #-}

  mplus = (<+>)
  {-# INLINE mplus #-}

instance (ArrowApply p, ArrowLoop p) => MonadFix (WrappedArrow p r) where
  mfix f = WrapArrow $ loop $ arr (\a -> (a, a)) . app . arr (\p -> (unwrapArrow (f $ snd p), fst p))
  {-# INLINE mfix #-}

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
