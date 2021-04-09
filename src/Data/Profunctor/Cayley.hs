{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE Trustworthy #-}

-- |
-- Copyright   :  (C) 2014-2021 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  portable

module Data.Profunctor.Cayley where

import Control.Applicative
import Control.Arrow as A
import Control.Category
import Control.Comonad
import Data.Biapplicative
import Data.Bifunctor as B
import Data.Bifunctor.Functor
import Data.Bifoldable
import Data.Bitraversable
import Data.Data
import Data.Profunctor
import Data.Profunctor.Functor
import Data.Profunctor.Monad
import Data.Profunctor.Traversing
import Data.Profunctor.Unsafe
import GHC.Generics
import Prelude hiding ((.), id)

-- | Static arrows. Lifted by 'Applicative'.
--
-- 'Cayley' has a polymorphic kind since @5.6@.

-- Cayley :: (k3 -> Type) -> (k1 -> k2 -> k3) -> (k1 -> k2 -> Type)
newtype Cayley f p a b = Cayley { runCayley :: f (p a b) }
  deriving (Generic, Generic1, Data)

deriving stock instance (Functor f, Functor (p a)) => Functor (Cayley f p a)
deriving stock instance (Foldable f, Foldable (p a)) => Foldable (Cayley f p a)
deriving stock instance (Traversable f, Traversable (p a)) => Traversable (Cayley f p a)

instance Functor f => ProfunctorFunctor (Cayley f) where
  promap = \f -> Cayley #. fmap f .# runCayley
  {-# inline promap #-}

-- | Cayley transforms Monads in @Hask@ into monads on @Prof@
instance Monad f => ProfunctorMonad (Cayley f) where
  proreturn = Cayley #. return
  {-# inline proreturn #-}
  projoin = \m -> Cayley $ runCayley m >>= runCayley
  {-# inline projoin #-}

-- | Cayley transforms Comonads in @Hask@ into comonads on @Prof@
instance Comonad f => ProfunctorComonad (Cayley f) where
  proextract = extract .# runCayley
  {-# inline proextract #-}
  produplicate = Cayley #. extend Cayley .# runCayley
  {-# inline produplicate #-}

instance (Functor f, Profunctor p) => Profunctor (Cayley f p) where
  dimap = \f g -> Cayley #. fmap (dimap f g) .# runCayley
  {-# inline dimap #-}
  lmap = \f -> Cayley #. fmap (lmap f) .# runCayley
  {-# inline lmap #-}
  rmap = \g -> Cayley #. fmap (rmap g) .# runCayley
  {-# inline rmap #-}
  (#.) = \w -> Cayley #. fmap (w #.) .# runCayley
  {-# inline (#.) #-}
  (.#) = \fp w -> Cayley $ fmap (.# w) (runCayley fp)
  {-# inline (.#) #-}

instance (Functor f, Bifunctor p) => Bifunctor (Cayley f p) where
  first = \f -> Cayley #. fmap (B.first f) .# runCayley
  {-# inline first #-}
  second = \f -> Cayley #. fmap (B.second f) .# runCayley
  {-# inline second #-}
  bimap = \f g -> Cayley #. fmap (bimap f g) .# runCayley
  {-# inline bimap #-}

instance (Applicative f, Biapplicative p) => Biapplicative (Cayley f p) where
  bipure = \a b -> Cayley $ pure $ bipure a b
  {-# inline bipure #-}

  (<<*>>) = \ fg -> Cayley #. liftA2 (<<*>>) (runCayley fg) .# runCayley
  {-# inline (<<*>>) #-}

instance (Foldable f, Bifoldable p) => Bifoldable (Cayley f p) where
  bifoldMap = \f g -> foldMap (bifoldMap f g) .# runCayley
  {-# inline bifoldMap #-}

instance (Traversable f, Bitraversable p) => Bitraversable (Cayley f p) where
  bitraverse = \f g -> fmap Cayley . traverse (bitraverse f g) .# runCayley
  {-# inline bitraverse #-}

instance Functor f => BifunctorFunctor (Cayley f) where
  bifmap = \f -> Cayley #. fmap f .# runCayley
  {-# inline bifmap #-}

instance (Functor f, Monad f) => BifunctorMonad (Cayley f) where
  bireturn = Cayley . return
  bibind = \f (Cayley fp) -> Cayley $ fp >>= runCayley . f
  {-# inline bireturn #-}
  {-# inline bibind #-}

instance Comonad f => BifunctorComonad (Cayley f) where
  biextract = extract .# runCayley
  biextend = \f -> Cayley #. extend (f .# Cayley) .# runCayley
  {-# inline biextract #-}
  {-# inline biextend #-}

instance (Functor f, Strong p) => Strong (Cayley f p) where
  first'  = Cayley #. fmap first' .# runCayley
  second' = Cayley #. fmap second' .# runCayley
  {-# inline first' #-}
  {-# inline second' #-}

instance (Functor f, Costrong p) => Costrong (Cayley f p) where
  unfirst = Cayley #. fmap unfirst .# runCayley
  unsecond = Cayley #. fmap unsecond .# runCayley
  {-# inline unfirst #-}
  {-# inline unsecond #-}

instance (Functor f, Choice p) => Choice (Cayley f p) where
  left' = Cayley #. fmap left' .# runCayley
  right' = Cayley #. fmap right' .# runCayley
  {-# inline left' #-}
  {-# inline right' #-}

instance (Functor f, Cochoice p) => Cochoice (Cayley f p) where
  unleft = Cayley #. fmap unleft .# runCayley
  {-# inline unleft #-}
  unright = Cayley #. fmap unright .# runCayley
  {-# inline unright #-}

instance (Functor f, Traversing p) => Traversing (Cayley f p) where
  traverse' = Cayley #. fmap traverse' .# runCayley
  {-# inline traverse' #-}

instance (Applicative f, Category p) => Category (Cayley f p) where
  id = Cayley $ pure id
  (.) = \fpbc -> Cayley #. liftA2 (.) (runCayley fpbc) .# runCayley
  {-# inline (.) #-}
  {-# inline id #-}

instance (Applicative f, Arrow p) => Arrow (Cayley f p) where
  arr = Cayley #. pure . arr
  first = Cayley #. fmap A.first .# runCayley
  second = Cayley #. fmap A.second .# runCayley
  (***) = \fpbc -> Cayley #. liftA2 (***) (runCayley fpbc) .# runCayley
  (&&&) = \fpbc -> Cayley #. liftA2 (&&&) (runCayley fpbc) .# runCayley
  {-# inline arr #-}
  {-# inline first #-}
  {-# inline (***) #-}
  {-# inline (&&&) #-}

instance (Applicative f, ArrowChoice p) => ArrowChoice (Cayley f p) where
  left  = Cayley #. fmap left .# runCayley
  right = Cayley #. fmap right .# runCayley
  (+++) = \fpbc -> Cayley #. liftA2 (+++) (runCayley fpbc) .# runCayley
  (|||) = \fpbc -> Cayley #. liftA2 (|||) (runCayley fpbc) .# runCayley
  {-# inline right #-}
  {-# inline left #-}
  {-# inline (+++) #-}
  {-# inline (|||) #-}

instance (Applicative f, ArrowLoop p) => ArrowLoop (Cayley f p) where
  loop = Cayley #. fmap loop .# runCayley
  {-# inline loop #-}

instance (Applicative f, ArrowZero p) => ArrowZero (Cayley f p) where
  zeroArrow = Cayley $ pure zeroArrow
  {-# inline zeroArrow #-}

instance (Applicative f, ArrowPlus p) => ArrowPlus (Cayley f p) where
  (<+>) = \fpbc -> Cayley #. liftA2 (<+>) (runCayley fpbc) .# runCayley
  {-# inline (<+>) #-}

mapCayley :: (forall a. f a -> g a) -> Cayley f p x y -> Cayley g p x y
mapCayley = \f -> Cayley #. f .# runCayley
{-# inline mapCayley #-}

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
