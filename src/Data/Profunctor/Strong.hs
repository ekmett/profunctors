{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}

#if __GLASGOW_HASKELL__ >= 704 && __GLASGOW_HASKELL__ < 708
{-# LANGUAGE Trustworthy #-}
#endif

-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2014 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  Rank2Types
--
----------------------------------------------------------------------------
module Data.Profunctor.Strong
  ( Strong(..)
  , uncurry'
  , Tambara(..)
  , tambara, untambara
  , Pastro(..)
  ) where

import Control.Applicative hiding (WrappedArrow(..))
import Control.Arrow
import Control.Category
import Control.Comonad
import Data.Bifunctor.Clown (Clown(..))
import Data.Bifunctor.Product (Product(..))
import Data.Bifunctor.Tannen (Tannen(..))
import Data.Functor.Contravariant (Contravariant(..))
import Data.Monoid hiding (Product)
import Data.Profunctor.Adjunction
import Data.Profunctor.Monad
import Data.Profunctor.Types
import Data.Profunctor.Unsafe
import Data.Tuple
import Prelude hiding (id,(.))

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

uncurry' :: Strong p => p a (b -> c) -> p (a, b) c
uncurry' = rmap (\(f,x) -> f x) . first'
{-# INLINE uncurry' #-}

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

instance Contravariant f => Strong (Clown f) where
  first' (Clown fa) = Clown (contramap fst fa)
  {-# INLINE first' #-}
  second' (Clown fa) = Clown (contramap snd fa)
  {-# INLINE second' #-}

instance (Strong p, Strong q) => Strong (Product p q) where
  first' (Pair p q) = Pair (first' p) (first' q)
  {-# INLINE first' #-}
  second' (Pair p q) = Pair (second' p) (second' q)
  {-# INLINE second' #-}

instance (Functor f, Strong p) => Strong (Tannen f p) where
  first' (Tannen fp) = Tannen (fmap first' fp)
  {-# INLINE first' #-}
  second' (Tannen fp) = Tannen (fmap second' fp)
  {-# INLINE second' #-}

----------------------------------------------------------------------------
-- * Tambara
----------------------------------------------------------------------------

-- | 'Tambara' cofreely makes any 'Profunctor' 'Strong'.
newtype Tambara p a b = Tambara { runTambara :: forall c. p (a, c) (b, c) }

instance Profunctor p => Profunctor (Tambara p) where
  dimap f g (Tambara p) = Tambara $ dimap (first f) (first g) p
  {-# INLINE dimap #-}

instance ProfunctorFunctor Tambara where
  promap f (Tambara p) = Tambara (f p)

instance ProfunctorComonad Tambara where
  proextract (Tambara p) = dimap (\a -> (a,())) fst p
  produplicate (Tambara p) = Tambara (Tambara $ dimap hither yon p) where
    hither :: ((a, b), c) -> (a, (b, c))
    hither ~(~(x,y),z) = (x,(y,z))

    yon    :: (a, (b, c)) -> ((a, b), c)
    yon    ~(x,~(y,z)) = ((x,y),z)

instance Profunctor p => Strong (Tambara p) where
  first' = runTambara . produplicate
  {-# INLINE first' #-}

instance Category p => Category (Tambara p) where
  id = Tambara id
  Tambara p . Tambara q = Tambara (p . q)

instance Arrow p => Arrow (Tambara p) where
  arr f = Tambara $ arr $ first f
  first (Tambara f) = Tambara (arr go . first f . arr go) where
    go :: ((a, b), c) -> ((a, c), b)
    go ~(~(x,y),z) = ((x,z),y)

instance ArrowChoice p => ArrowChoice (Tambara p) where
  left (Tambara f) = Tambara (arr yon . left f . arr hither) where
    hither :: (Either a b, c) -> Either (a, c) (b, c)
    hither (Left y, s) = Left (y, s)
    hither (Right z, s) = Right (z, s)

    yon :: Either (a, c) (b, c) -> (Either a b, c)
    yon (Left (y, s)) = (Left y, s)
    yon (Right (z, s)) = (Right z, s)

instance ArrowApply p => ArrowApply (Tambara p) where
  app = Tambara $ app . arr (\((Tambara f, x), s) -> (f, (x, s)))

instance ArrowLoop p => ArrowLoop (Tambara p) where
  loop (Tambara f) = Tambara (loop (arr go . f . arr go)) where
    go :: ((a, b), c) -> ((a, c), b)
    go ~(~(x,y),z) = ((x,z),y)

instance ArrowZero p => ArrowZero (Tambara p) where
  zeroArrow = Tambara zeroArrow

instance ArrowPlus p => ArrowPlus (Tambara p) where
  Tambara f <+> Tambara g = Tambara (f <+> g)

instance Profunctor p => Functor (Tambara p a) where
  fmap = rmap

instance (Profunctor p, Arrow p) => Applicative (Tambara p a) where
  pure x = arr (const x)
  f <*> g = arr (uncurry id) . (f &&& g)

instance (Profunctor p, ArrowPlus p) => Alternative (Tambara p a) where
  empty = zeroArrow
  f <|> g = f <+> g

instance (Profunctor p, ArrowPlus p) => Monoid (Tambara p a b) where
  mempty = zeroArrow
  mappend f g = f <+> g

-- |
-- @
-- 'tambara' '.' 'untambara' ≡ 'id'
-- 'untambara' '.' 'tambara' ≡ 'id'
-- @
tambara :: Strong p => (p :-> q) -> p :-> Tambara q
tambara f p = Tambara $ f $ first' p

-- |
-- @
-- 'tambara' '.' 'untambara' ≡ 'id'
-- 'untambara' '.' 'tambara' ≡ 'id'
-- @
untambara :: Profunctor q => (p :-> Tambara q) -> p :-> q
untambara f p = dimap (\a -> (a,())) fst $ runTambara $ f p

----------------------------------------------------------------------------
-- * Pastro
----------------------------------------------------------------------------

-- | Pastro -| Tambara
--
-- @
-- Pastro p ~ exists z. Costar ((,)z) `Procompose` p `Procompose` Star ((,)z)
-- @
--
-- 'Pastro' freely makes any 'Profunctor' 'Strong'.
data Pastro p a b where
  Pastro :: ((y, z) -> b) -> p x y -> (a -> (x, z)) -> Pastro p a b

instance Profunctor p => Profunctor (Pastro p) where
  dimap f g (Pastro l m r) = Pastro (g . l) m (r . f)
  lmap f (Pastro l m r) = Pastro l m (r . f)
  rmap g (Pastro l m r) = Pastro (g . l) m r
  w #. Pastro l m r = Pastro (w #. l) m r
  Pastro l m r .# w = Pastro l m (r .# w)

instance ProfunctorFunctor Pastro where
  promap f (Pastro l m r) = Pastro l (f m) r

instance ProfunctorMonad Pastro where
  proreturn p = Pastro fst p $ \a -> (a,())
  projoin (Pastro l (Pastro m n o) p) = Pastro lm n op where
    op a = case p a of
      (b, f) -> case o b of
         (c, g) -> (c, (f, g))
    lm (d, (f, g)) = l (m (d, g), f)

instance ProfunctorAdjunction Pastro Tambara where
  counit (Pastro g (Tambara p) f) = dimap f g p
  unit p = Tambara (Pastro id p id)

instance Profunctor p => Strong (Pastro p) where
  first' (Pastro l m r) = Pastro l' m r' where
    r' (a,c) = case r a of
      (x,z) -> (x,(z,c))
    l' (y,(z,c)) = (l (y,z), c)
  second' (Pastro l m r) = Pastro l' m r' where
    r' (c,a) = case r a of
      (x,z) -> (x,(c,z))
    l' (y,(c,z)) = (c,l (y,z))

