{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Trustworthy #-}
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2014-2015 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  portable
--
----------------------------------------------------------------------------

module Data.Profunctor.Cayley where

import Control.Applicative
import Control.Arrow
import Control.Category
import Control.Comonad
import Data.Profunctor
import Data.Profunctor.Monad
import Data.Profunctor.Traversing
import Data.Profunctor.Unsafe
import Prelude hiding ((.), id)

-- | Static arrows. Lifted by 'Applicative'.
--
-- 'Cayley' has a polymorphic kind since @5.6@.

-- Cayley :: (k3 -> Type) -> (k1 -> k2 -> k3) -> (k1 -> k2 -> Type)
newtype Cayley f p a b = Cayley { runCayley :: f (p a b) }

instance Functor f => ProfunctorFunctor (Cayley f) where
  promap f (Cayley p) = Cayley (fmap f p)

-- | Cayley transforms Monads in @Hask@ into monads on @Prof@
instance (Functor f, Monad f) => ProfunctorMonad (Cayley f) where
  proreturn = Cayley . return
  projoin (Cayley m) = Cayley $ m >>= runCayley

-- | Cayley transforms Comonads in @Hask@ into comonads on @Prof@
instance Comonad f => ProfunctorComonad (Cayley f) where
  proextract = extract . runCayley
  produplicate (Cayley w) = Cayley $ extend Cayley w

instance (Functor f, Profunctor p) => Profunctor (Cayley f p) where
  dimap f g = Cayley . fmap (dimap f g) . runCayley
  lmap f = Cayley . fmap (lmap f) . runCayley
  rmap g = Cayley . fmap (rmap g) . runCayley
  w #. Cayley fp = Cayley $ fmap (w #.) fp
  Cayley fp .# w = Cayley $ fmap (.# w) fp

instance (Functor f, Strong p) => Strong (Cayley f p) where
  first'  = Cayley . fmap first' . runCayley
  second' = Cayley . fmap second' . runCayley

instance (Functor f, Costrong p) => Costrong (Cayley f p) where
  unfirst (Cayley fp) = Cayley (fmap unfirst fp)
  unsecond (Cayley fp) = Cayley (fmap unsecond fp)

instance (Functor f, Choice p) => Choice (Cayley f p) where
  left'   = Cayley . fmap left' . runCayley
  right'  = Cayley . fmap right' . runCayley

instance (Functor f, Cochoice p) => Cochoice (Cayley f p) where
  unleft (Cayley fp) = Cayley (fmap unleft fp)
  {-# INLINE unleft #-}
  unright (Cayley fp) = Cayley (fmap unright fp)
  {-# INLINE unright #-}

instance (Functor f, Closed p) => Closed (Cayley f p) where
  closed = Cayley . fmap closed . runCayley

instance (Functor f, Traversing p) => Traversing (Cayley f p) where
  traverse' = Cayley . fmap traverse' . runCayley

instance (Functor f, Mapping p) => Mapping (Cayley f p) where
  map' = Cayley . fmap map' . runCayley

instance (Applicative f, Category p) => Category (Cayley f p) where
  id = Cayley $ pure id
  Cayley fpbc . Cayley fpab = Cayley $ liftA2 (.) fpbc fpab

instance (Applicative f, Arrow p) => Arrow (Cayley f p) where
  arr f = Cayley $ pure $ arr f
  first = Cayley . fmap first . runCayley
  second = Cayley . fmap second . runCayley
  Cayley ab *** Cayley cd = Cayley $ liftA2 (***) ab cd
  Cayley ab &&& Cayley ac = Cayley $ liftA2 (&&&) ab ac

instance (Applicative f, ArrowChoice p) => ArrowChoice (Cayley f p) where
  left  = Cayley . fmap left . runCayley
  right = Cayley . fmap right . runCayley
  Cayley ab +++ Cayley cd = Cayley $ liftA2 (+++) ab cd
  Cayley ac ||| Cayley bc = Cayley $ liftA2 (|||) ac bc

instance (Applicative f, ArrowLoop p) => ArrowLoop (Cayley f p) where
  loop = Cayley . fmap loop . runCayley

instance (Applicative f, ArrowZero p) => ArrowZero (Cayley f p) where
  zeroArrow = Cayley $ pure zeroArrow

instance (Applicative f, ArrowPlus p) => ArrowPlus (Cayley f p) where
  Cayley f <+> Cayley g = Cayley (liftA2 (<+>) f g)

mapCayley :: (forall a. f a -> g a) -> Cayley f p x y -> Cayley g p x y
mapCayley f (Cayley g) = Cayley (f g)

-- instance Adjunction f g => ProfunctorAdjunction (Cayley f) (Cayley g) where

{-
newtype Uncayley p a = Uncayley (p () a)

instance Profunctor p => Functor (Uncayley p) where
  fmap f (Uncayley p) = Uncayley (rmap f p)

smash :: Strong p => Cayley (Uncayley p) (->) a b -> p a b
smash (Cayley (Uncayley pab)) = dimap ((,)()) (uncurry id) (first' pab)

unsmash :: Closed p => p a b -> Cayley (Uncayley p) (->) a b
unsmash = Cayley . Uncayley . curry' . lmap snd

type Iso s t a b = forall p f. (Profunctor p, Functor f) => p a (f b) -> p s (f t)

-- pastro and street's strong tambara module
class (Strong p, Closed p) => Stronger p

-- only a true iso for Stronger p and q, no?
_Smash :: (Strong p, Closed q) => Iso
  (Cayley (Uncayley p) (->) a b)
  (Cayley (Uncayley q) (->) c d)
  (p a b)
  (q c d)
_Smash = dimap hither (fmap yon) where
  hither (Cayley (Uncayley pab)) = dimap ((,)()) (uncurry id) (first' pab)
  yon = Cayley . Uncayley . curry' . lmap snd

fsmash :: (forall x y. p x y -> q x y) -> Cayley (Uncayley p) (->) a b -> Cayley (Uncayley q) (->) a b
fsmash f (Cayley (Uncayley puab)) = Cayley (Uncayley (f puab))

-- | proposition 4.3 from pastro and street is that fsmash and funsmash form an equivalence of categories
funsmash :: (Closed p, Strong q) => (forall x y. Cayley (Uncayley p) (->) x y -> Cayley (Uncayley q) (->) x y) -> p a b -> q a b
funsmash k = smash . k . unsmash
-}
