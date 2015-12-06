{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Data.Profunctor.Mapping
  ( Mapping(..)
  , CofreeMapping(..)
  , FreeMapping(..)
  -- * Strong in terms of Mapping
  , firstMapping
  , secondMapping
  -- * Choice in terms of Mapping
  , leftMapping
  , rightMapping
  -- * Closed in terms of Mapping
  , closedMapping
  ) where

import Data.Functor.Compose
import Data.Functor.Identity
import Data.Profunctor.Choice
import Data.Profunctor.Closed
import Data.Profunctor.Monad
import Data.Profunctor.Strong
import Data.Profunctor.Types
import Data.Profunctor.Unsafe
import Data.Tuple (swap)

firstMapping :: Mapping p => p a b -> p (a, c) (b, c)
firstMapping = dimap swap swap . map'

secondMapping :: Mapping p => p a b -> p (c, a) (c, b)
secondMapping = map'

swapE :: Either a b -> Either b a
swapE = either Right Left

leftMapping :: Mapping p => p a b -> p (Either a c) (Either b c)
leftMapping = dimap swapE swapE . map'

rightMapping :: Mapping p => p a b -> p (Either c a) (Either c b)
rightMapping = map'

closedMapping :: Mapping p => p a b -> p (x -> a) (x -> b)
closedMapping = map'

class (Choice p, Strong p, Closed p) => Mapping p where
  map' :: Functor f => p a b -> p (f a) (f b)

instance Mapping (->) where
  map' = fmap

newtype CofreeMapping p a b = CofreeMapping { runCofreeMapping :: forall f. Functor f => p (f a) (f b) }

instance Profunctor p => Profunctor (CofreeMapping p) where
  lmap f (CofreeMapping p) = CofreeMapping (lmap (fmap f) p)
  rmap g (CofreeMapping p) = CofreeMapping (rmap (fmap g) p)
  dimap f g (CofreeMapping p) = CofreeMapping (dimap (fmap f) (fmap g) p)

instance Profunctor p => Strong (CofreeMapping p) where
  second' = map'

instance Profunctor p => Choice (CofreeMapping p) where
  right' = map'

instance Profunctor p => Closed (CofreeMapping p) where
  closed = map'

instance Profunctor p => Mapping (CofreeMapping p) where
  -- !@(#*&() Compose isn't representational in its second arg or we could use #. and .#
  map' (CofreeMapping p) = CofreeMapping (dimap Compose getCompose p)

instance ProfunctorFunctor CofreeMapping where
  promap f (CofreeMapping p) = CofreeMapping (f p)

instance ProfunctorComonad CofreeMapping where
  proextract (CofreeMapping p) = runIdentity #. p .# Identity
  produplicate (CofreeMapping p) = CofreeMapping (CofreeMapping (dimap Compose getCompose p))

-- | @FreeMapping -| CofreeMapping@
data FreeMapping p a b where
  FreeMapping :: Functor f => (f y -> b) -> p x y -> (a -> f x) -> FreeMapping p a b

instance Profunctor (FreeMapping p) where
  lmap f (FreeMapping l m r) = FreeMapping l m (r . f)
  rmap g (FreeMapping l m r) = FreeMapping (g . l) m r
  dimap f g (FreeMapping l m r) = FreeMapping (g . l) m (r . f)
  g #. FreeMapping l m r = FreeMapping (g #. l) m r
  FreeMapping l m r .# f = FreeMapping l m (r .# f)

instance Strong (FreeMapping p) where
  second' = map'

instance Choice (FreeMapping p) where
  right' = map'

instance Closed (FreeMapping p) where
  closed = map'

instance Mapping (FreeMapping p) where
  map' (FreeMapping l m r) = FreeMapping (fmap l .# getCompose) m (Compose #. fmap r)

instance ProfunctorFunctor FreeMapping where
  promap f (FreeMapping l m r) = FreeMapping l (f m) r

instance ProfunctorMonad FreeMapping where
  proreturn p = FreeMapping runIdentity p Identity
  projoin (FreeMapping l (FreeMapping l' m r') r) = FreeMapping ((l . fmap l') .# getCompose) m (Compose #. (fmap r' . r))
