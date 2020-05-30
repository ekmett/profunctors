{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Profunctor.Composition
-- Copyright   :  (C) 2014-2015 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  GADTs, TFs, MPTCs, RankN
--
----------------------------------------------------------------------------
module Data.Profunctor.Composition
  (
  -- * Profunctor Composition
    Procompose(..)
  , procomposed
  -- * Unitors and Associator
  , idl
  , idr
  , assoc
  -- * Categories as monoid objects
  , eta
  , mu
  -- * Generalized Composition
  , stars, kleislis
  , costars, cokleislis
  -- * Right Kan Lift
  , Rift(..)
  , decomposeRift
  ) where

import Control.Arrow
import Control.Category
import Control.Comonad
import Control.Monad (liftM)
import Data.Functor.Compose
import Data.Profunctor
import Data.Profunctor.Adjunction
import Data.Profunctor.Monad
import Data.Profunctor.Rep
import Data.Profunctor.Sieve
import Data.Profunctor.Traversing
import Data.Profunctor.Unsafe
import Prelude hiding ((.),id)

type Iso s t a b = forall p f. (Profunctor p, Functor f) => p a (f b) -> p s (f t)

-- * Profunctor Composition

-- | @'Procompose' p q@ is the 'Profunctor' composition of the
-- 'Profunctor's @p@ and @q@.
--
-- For a good explanation of 'Profunctor' composition in Haskell
-- see Dan Piponi's article:
--
-- <http://blog.sigfpe.com/2011/07/profunctors-in-haskell.html>
--
-- 'Procompose' has a polymorphic kind since @5.6@.

-- Procompose :: (k1 -> k2 -> Type) -> (k3 -> k1 -> Type) -> (k3 -> k2 -> Type)
data Procompose p q d c where
  Procompose :: p x c -> q d x -> Procompose p q d c

instance ProfunctorFunctor (Procompose p) where
  promap f (Procompose p q) = Procompose p (f q)

instance Category p => ProfunctorMonad (Procompose p) where
  proreturn = Procompose id
  projoin (Procompose p (Procompose q r)) = Procompose (p . q) r

procomposed :: Category p => Procompose p p a b -> p a b
procomposed (Procompose pxc pdx) = pxc . pdx
{-# INLINE procomposed #-}

instance (Profunctor p, Profunctor q) => Profunctor (Procompose p q) where
  dimap l r (Procompose f g) = Procompose (rmap r f) (lmap l g)
  {-# INLINE dimap #-}
  lmap k (Procompose f g) = Procompose f (lmap k g)
  {-# INLINE rmap #-}
  rmap k (Procompose f g) = Procompose (rmap k f) g
  {-# INLINE lmap #-}
  k #. Procompose f g     = Procompose (k #. f) g
  {-# INLINE (#.) #-}
  Procompose f g .# k     = Procompose f (g .# k)
  {-# INLINE (.#) #-}

instance Profunctor p => Functor (Procompose p q a) where
  fmap k (Procompose f g) = Procompose (rmap k f) g
  {-# INLINE fmap #-}

instance (Sieve p f, Sieve q g) => Sieve (Procompose p q) (Compose g f) where
  sieve (Procompose g f) d = Compose $ sieve g <$> sieve f d
  {-# INLINE sieve #-}

-- | The composition of two 'Representable' 'Profunctor's is 'Representable' by
-- the composition of their representations.
instance (Representable p, Representable q) => Representable (Procompose p q) where
  type Rep (Procompose p q) = Compose (Rep q) (Rep p)
  tabulate f = Procompose (tabulate id) (tabulate (getCompose . f))
  {-# INLINE tabulate #-}

instance (Cosieve p f, Cosieve q g) => Cosieve (Procompose p q) (Compose f g) where
  cosieve (Procompose g f) (Compose d) = cosieve g $ cosieve f <$> d
  {-# INLINE cosieve #-}

instance (Corepresentable p, Corepresentable q) => Corepresentable (Procompose p q) where
  type Corep (Procompose p q) = Compose (Corep p) (Corep q)
  cotabulate f = Procompose (cotabulate (f . Compose)) (cotabulate id)
  {-# INLINE cotabulate #-}

instance (Strong p, Strong q) => Strong (Procompose p q) where
  first' (Procompose x y) = Procompose (first' x) (first' y)
  {-# INLINE first' #-}
  second' (Procompose x y) = Procompose (second' x) (second' y)
  {-# INLINE second' #-}

instance (Choice p, Choice q) => Choice (Procompose p q) where
  left' (Procompose x y) = Procompose (left' x) (left' y)
  {-# INLINE left' #-}
  right' (Procompose x y) = Procompose (right' x) (right' y)
  {-# INLINE right' #-}

instance (Closed p, Closed q) => Closed (Procompose p q) where
  closed (Procompose x y) = Procompose (closed x) (closed y)
  {-# INLINE closed #-}

instance (Traversing p, Traversing q) => Traversing (Procompose p q) where
  traverse' (Procompose p q) = Procompose (traverse' p) (traverse' q)
  {-# INLINE traverse' #-}

instance (Mapping p, Mapping q) => Mapping (Procompose p q) where
  map' (Procompose p q) = Procompose (map' p) (map' q)
  {-# INLINE map' #-}

instance (Corepresentable p, Corepresentable q) => Costrong (Procompose p q) where
  unfirst = unfirstCorep
  {-# INLINE unfirst #-}
  unsecond = unsecondCorep
  {-# INLINE unsecond #-}

-- * Lax identity

-- | @(->)@ functions as a lax identity for 'Profunctor' composition.
--
-- This provides an 'Iso' for the @lens@ package that witnesses the
-- isomorphism between @'Procompose' (->) q d c@ and @q d c@, which
-- is the left identity law.
--
-- @
-- 'idl' :: 'Profunctor' q => Iso' ('Procompose' (->) q d c) (q d c)
-- @
idl :: Profunctor q => Iso (Procompose (->) q d c) (Procompose (->) r d' c') (q d c) (r d' c')
idl = dimap (\(Procompose g f) -> rmap g f) (fmap (Procompose id))

-- | @(->)@ functions as a lax identity for 'Profunctor' composition.
--
-- This provides an 'Iso' for the @lens@ package that witnesses the
-- isomorphism between @'Procompose' q (->) d c@ and @q d c@, which
-- is the right identity law.
--
-- @
-- 'idr' :: 'Profunctor' q => Iso' ('Procompose' q (->) d c) (q d c)
-- @
idr :: Profunctor q => Iso (Procompose q (->) d c) (Procompose r (->) d' c') (q d c) (r d' c')
idr = dimap (\(Procompose g f) -> lmap f g) (fmap (`Procompose` id))


-- | The associator for 'Profunctor' composition.
--
-- This provides an 'Iso' for the @lens@ package that witnesses the
-- isomorphism between @'Procompose' p ('Procompose' q r) a b@ and
-- @'Procompose' ('Procompose' p q) r a b@, which arises because
-- @Prof@ is only a bicategory, rather than a strict 2-category.
assoc :: Iso (Procompose p (Procompose q r) a b) (Procompose x (Procompose y z) a b)
             (Procompose (Procompose p q) r a b) (Procompose (Procompose x y) z a b)
assoc = dimap (\(Procompose f (Procompose g h)) -> Procompose (Procompose f g) h)
              (fmap (\(Procompose (Procompose f g) h) -> Procompose f (Procompose g h)))

-- | 'Profunctor' composition generalizes 'Functor' composition in two ways.
--
-- This is the first, which shows that @exists b. (a -> f b, b -> g c)@ is
-- isomorphic to @a -> f (g c)@.
--
-- @'stars' :: 'Functor' f => Iso' ('Procompose' ('Star' f) ('Star' g) d c) ('Star' ('Compose' f g) d c)@
stars :: Functor g
        => Iso (Procompose (Star f ) (Star g ) d  c )
               (Procompose (Star f') (Star g') d' c')
               (Star (Compose g  f ) d  c )
               (Star (Compose g' f') d' c')
stars = dimap hither (fmap yon) where
  hither (Procompose (Star xgc) (Star dfx)) = Star (Compose . fmap xgc . dfx)
  yon (Star dfgc) = Procompose (Star id) (Star (getCompose . dfgc))

-- | 'Profunctor' composition generalizes 'Functor' composition in two ways.
--
-- This is the second, which shows that @exists b. (f a -> b, g b -> c)@ is
-- isomorphic to @g (f a) -> c@.
--
-- @'costars' :: 'Functor' f => Iso' ('Procompose' ('Costar' f) ('Costar' g) d c) ('Costar' ('Compose' g f) d c)@
costars :: Functor f
          => Iso (Procompose (Costar f ) (Costar g ) d  c )
                 (Procompose (Costar f') (Costar g') d' c')
                 (Costar (Compose f  g ) d  c )
                 (Costar (Compose f' g') d' c')
costars = dimap hither (fmap yon) where
  hither (Procompose (Costar gxc) (Costar fdx)) = Costar (gxc . fmap fdx . getCompose)
  yon (Costar dgfc) = Procompose (Costar (dgfc . Compose)) (Costar id)

-- | This is a variant on 'stars' that uses 'Kleisli' instead of 'Star'.
--
-- @'kleislis' :: 'Monad' f => Iso' ('Procompose' ('Kleisli' f) ('Kleisli' g) d c) ('Kleisli' ('Compose' f g) d c)@
kleislis :: Monad g
        => Iso (Procompose (Kleisli f ) (Kleisli g ) d  c )
               (Procompose (Kleisli f') (Kleisli g') d' c')
               (Kleisli (Compose g  f ) d  c )
               (Kleisli (Compose g' f') d' c')
kleislis = dimap hither (fmap yon) where
  hither (Procompose (Kleisli xgc) (Kleisli dfx)) = Kleisli (Compose . liftM xgc . dfx)
  yon (Kleisli dfgc) = Procompose (Kleisli id) (Kleisli (getCompose . dfgc))

-- | This is a variant on 'costars' that uses 'Cokleisli' instead
-- of 'Costar'.
--
-- @'cokleislis' :: 'Functor' f => Iso' ('Procompose' ('Cokleisli' f) ('Cokleisli' g) d c) ('Cokleisli' ('Compose' g f) d c)@
cokleislis :: Functor f
          => Iso (Procompose (Cokleisli f ) (Cokleisli g ) d  c )
                 (Procompose (Cokleisli f') (Cokleisli g') d' c')
                 (Cokleisli (Compose f  g ) d  c )
                 (Cokleisli (Compose f' g') d' c')
cokleislis = dimap hither (fmap yon) where
  hither (Procompose (Cokleisli gxc) (Cokleisli fdx)) = Cokleisli (gxc . fmap fdx . getCompose)
  yon (Cokleisli dgfc) = Procompose (Cokleisli (dgfc . Compose)) (Cokleisli id)

----------------------------------------------------------------------------
-- * Rift
----------------------------------------------------------------------------

-- | This represents the right Kan lift of a 'Profunctor' @q@ along a
-- 'Profunctor' @p@ in a limited version of the 2-category of Profunctors where
-- the only object is the category Hask, 1-morphisms are profunctors composed
-- and compose with Profunctor composition, and 2-morphisms are just natural
-- transformations.
--
-- 'Rift' has a polymorphic kind since @5.6@.

-- Rift :: (k3 -> k2 -> Type) -> (k1 -> k2 -> Type) -> (k1 -> k3 -> Type)
newtype Rift p q a b = Rift { runRift :: forall x. p b x -> q a x }

instance ProfunctorFunctor (Rift p) where
  promap f (Rift g) = Rift (f . g)

instance Category p => ProfunctorComonad (Rift p) where
  proextract (Rift f) = f id
  produplicate (Rift f) = Rift $ \p -> Rift $ \q -> f (q . p)

instance (Profunctor p, Profunctor q) => Profunctor (Rift p q) where
  dimap ca bd f = Rift (lmap ca . runRift f . lmap bd)
  {-# INLINE dimap #-}
  lmap ca f = Rift (lmap ca . runRift f)
  {-# INLINE lmap #-}
  rmap bd f = Rift (runRift f . lmap bd)
  {-# INLINE rmap #-}
  bd #. f = Rift (\p -> runRift f (p .# bd))
  {-# INLINE (#.) #-}
  f .# ca = Rift (\p -> runRift f p .# ca)
  {-# INLINE (.#) #-}

instance Profunctor p => Functor (Rift p q a) where
  fmap bd f = Rift (runRift f . lmap bd)
  {-# INLINE fmap #-}

-- | @'Rift' p p@ forms a 'Monad' in the 'Profunctor' 2-category, which is isomorphic to a Haskell 'Category' instance.
instance p ~ q => Category (Rift p q) where
  id = Rift id
  {-# INLINE id #-}
  Rift f . Rift g = Rift (g . f)
  {-# INLINE (.) #-}

-- | The 2-morphism that defines a left Kan lift.
--
-- Note: When @p@ is right adjoint to @'Rift' p (->)@ then 'decomposeRift' is the 'counit' of the adjunction.
decomposeRift :: Procompose p (Rift p q) :-> q
decomposeRift (Procompose p (Rift pq)) = pq p
{-# INLINE decomposeRift #-}

instance ProfunctorAdjunction (Procompose p) (Rift p) where
  counit (Procompose p (Rift pq)) = pq p
  unit q = Rift $ \p -> Procompose p q

--instance (ProfunctorAdjunction f g, ProfunctorAdjunction f' g') => ProfunctorAdjunction (ProfunctorCompose f' f) (ProfunctorCompose g g') where

----------------------------------------------------------------------------
-- * Monoids
----------------------------------------------------------------------------


-- | a 'Category' that is also a 'Profunctor' is a 'Monoid' in @Prof@

eta :: (Profunctor p, Category p) => (->) :-> p
eta f = rmap f id

mu :: Category p => Procompose p p :-> p
mu (Procompose f g) = f . g
