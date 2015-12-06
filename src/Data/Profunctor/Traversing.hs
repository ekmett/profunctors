{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Data.Profunctor.Traversing
  ( Traversing(..)
  , CofreeTraversing(..)
  , FreeTraversing(..)
  -- * Strong in terms of Traversing
  , firstTraversing
  , secondTraversing
  -- * Choice in terms of Traversing
  , leftTraversing
  , rightTraversing
  ) where

import Control.Arrow (Kleisli(..))
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Profunctor.Choice
import Data.Profunctor.Monad
import Data.Profunctor.Strong
import Data.Profunctor.Types
import Data.Profunctor.Unsafe
#if __GLASGOW_HASKELL__ < 710
import Data.Traversable
#endif
import Data.Tuple (swap)

firstTraversing :: Traversing p => p a b -> p (a, c) (b, c)
firstTraversing = dimap swap swap . traverse'

secondTraversing :: Traversing p => p a b -> p (c, a) (c, b)
secondTraversing = traverse'

swapE :: Either a b -> Either b a
swapE = either Right Left

leftTraversing :: Traversing p => p a b -> p (Either a c) (Either b c)
leftTraversing = dimap swapE swapE . traverse'

rightTraversing :: Traversing p => p a b -> p (Either c a) (Either c b)
rightTraversing = traverse'

class (Choice p, Strong p) => Traversing p where
  traverse' :: Traversable f => p a b -> p (f a) (f b)

instance Traversing (->) where
  traverse' = fmap

instance Monad m => Traversing (Kleisli m) where
  traverse' (Kleisli m) = Kleisli (mapM m)

instance Applicative m => Traversing (Star m) where
  traverse' (Star m) = Star (traverse m)

newtype CofreeTraversing p a b = CofreeTraversing { runCofreeTraversing :: forall f. Traversable f => p (f a) (f b) }

instance Profunctor p => Profunctor (CofreeTraversing p) where
  lmap f (CofreeTraversing p) = CofreeTraversing (lmap (fmap f) p)
  rmap g (CofreeTraversing p) = CofreeTraversing (rmap (fmap g) p)
  dimap f g (CofreeTraversing p) = CofreeTraversing (dimap (fmap f) (fmap g) p)

instance Profunctor p => Strong (CofreeTraversing p) where
  second' = traverse'

instance Profunctor p => Choice (CofreeTraversing p) where
  right' = traverse'

instance Profunctor p => Traversing (CofreeTraversing p) where
  -- !@(#*&() Compose isn't representational in its second arg or we could use #. and .#
  traverse' (CofreeTraversing p) = CofreeTraversing (dimap Compose getCompose p)

instance ProfunctorFunctor CofreeTraversing where
  promap f (CofreeTraversing p) = CofreeTraversing (f p)

instance ProfunctorComonad CofreeTraversing where
  proextract (CofreeTraversing p) = runIdentity #. p .# Identity
  produplicate (CofreeTraversing p) = CofreeTraversing (CofreeTraversing (dimap Compose getCompose p))

-- | @FreeTraversing -| CofreeTraversing@
data FreeTraversing p a b where
  FreeTraversing :: Traversable f => (f y -> b) -> p x y -> (a -> f x) -> FreeTraversing p a b

instance Profunctor (FreeTraversing p) where
  lmap f (FreeTraversing l m r) = FreeTraversing l m (r . f)
  rmap g (FreeTraversing l m r) = FreeTraversing (g . l) m r
  dimap f g (FreeTraversing l m r) = FreeTraversing (g . l) m (r . f)
  g #. FreeTraversing l m r = FreeTraversing (g #. l) m r
  FreeTraversing l m r .# f = FreeTraversing l m (r .# f)

instance Strong (FreeTraversing p) where
  second' = traverse'

instance Choice (FreeTraversing p) where
  right' = traverse'

instance Traversing (FreeTraversing p) where
  traverse' (FreeTraversing l m r) = FreeTraversing (fmap l .# getCompose) m (Compose #. fmap r)

instance ProfunctorFunctor FreeTraversing where
  promap f (FreeTraversing l m r) = FreeTraversing l (f m) r

instance ProfunctorMonad FreeTraversing where
  proreturn p = FreeTraversing runIdentity p Identity
  projoin (FreeTraversing l (FreeTraversing l' m r') r) = FreeTraversing ((l . fmap l') .# getCompose) m (Compose #. (fmap r' . r))
