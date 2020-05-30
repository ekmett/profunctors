{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Profunctor.Rep
-- Copyright   :  (C) 2011-2015 Edward Kmett,
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  Type-Families
--
----------------------------------------------------------------------------
module Data.Profunctor.Rep
  (
  -- * Representable Profunctors
    Representable(..)
  , tabulated
  , firstRep, secondRep
  -- * Corepresentable Profunctors
  , Corepresentable(..)
  , cotabulated
  , unfirstCorep, unsecondCorep
  , closedCorep
  -- * Prep -| Star
  , Prep(..)
  , prepAdj
  , unprepAdj
  , prepUnit
  , prepCounit
  -- * Coprep -| Costar
  , Coprep(..)
  , coprepAdj
  , uncoprepAdj
  , coprepUnit
  , coprepCounit
  ) where

import Control.Applicative
import Control.Arrow
import Control.Comonad
import Control.Monad ((>=>))
import Data.Functor.Identity
import Data.Profunctor
import Data.Profunctor.Sieve
import Data.Proxy
import Data.Tagged

-- * Representable Profunctors

-- | A 'Profunctor' @p@ is 'Representable' if there exists a 'Functor' @f@ such that
-- @p d c@ is isomorphic to @d -> f c@.
class (Sieve p (Rep p), Strong p) => Representable p where
  type Rep p :: * -> *
  -- | Laws:
  --
  -- @
  -- 'tabulate' '.' 'sieve' ≡ 'id'
  -- 'sieve' '.' 'tabulate' ≡ 'id'
  -- @
  tabulate :: (d -> Rep p c) -> p d c

-- | Default definition for 'first'' given that p is 'Representable'.
firstRep :: Representable p => p a b -> p (a, c) (b, c)
firstRep p = tabulate $ \(a,c) -> (\b -> (b, c)) <$> sieve p a

-- | Default definition for 'second'' given that p is 'Representable'.
secondRep :: Representable p => p a b -> p (c, a) (c, b)
secondRep p = tabulate $ \(c,a) -> (,) c <$> sieve p a

instance Representable (->) where
  type Rep (->) = Identity
  tabulate f = runIdentity . f
  {-# INLINE tabulate #-}

instance (Monad m, Functor m) => Representable (Kleisli m) where
  type Rep (Kleisli m) = m
  tabulate = Kleisli
  {-# INLINE tabulate #-}

instance Functor f => Representable (Star f) where
  type Rep (Star f) = f
  tabulate = Star
  {-# INLINE tabulate #-}

instance Representable (Forget r) where
  type Rep (Forget r) = Const r
  tabulate = Forget . (getConst .)
  {-# INLINE tabulate #-}

{- TODO: coproducts and products
instance (Representable p, Representable q) => Representable (Bifunctor.Product p q)
  type Rep (Bifunctor.Product p q) = Functor.Product p q

instance (Corepresentable p, Corepresentable q) => Corepresentable (Bifunctor.Product p q) where
  type Rep (Bifunctor.Product p q) = Functor.Sum p q
-}

type Iso s t a b = forall p f. (Profunctor p, Functor f) => p a (f b) -> p s (f t)

-- | 'tabulate' and 'sieve' form two halves of an isomorphism.
--
-- This can be used with the combinators from the @lens@ package.
--
-- @'tabulated' :: 'Representable' p => 'Iso'' (d -> 'Rep' p c) (p d c)@
tabulated :: (Representable p, Representable q) => Iso (d -> Rep p c) (d' -> Rep q c') (p d c) (q d' c')
tabulated = dimap tabulate (fmap sieve)
{-# INLINE tabulated #-}

-- * Corepresentable Profunctors

-- | A 'Profunctor' @p@ is 'Corepresentable' if there exists a 'Functor' @f@ such that
-- @p d c@ is isomorphic to @f d -> c@.
class (Cosieve p (Corep p), Costrong p) => Corepresentable p where
  type Corep p :: * -> *
  -- | Laws:
  --
  -- @
  -- 'cotabulate' '.' 'cosieve' ≡ 'id'
  -- 'cosieve' '.' 'cotabulate' ≡ 'id'
  -- @
  cotabulate :: (Corep p d -> c) -> p d c

-- | Default definition for 'unfirst' given that @p@ is 'Corepresentable'.
unfirstCorep :: Corepresentable p => p (a, d) (b, d) -> p a b
unfirstCorep p = cotabulate f
  where f fa = b where (b, d) = cosieve p ((\a -> (a, d)) <$> fa)

-- | Default definition for 'unsecond' given that @p@ is 'Corepresentable'.
unsecondCorep :: Corepresentable p => p (d, a) (d, b) -> p a b
unsecondCorep p = cotabulate f
  where f fa = b where (d, b) = cosieve p ((,) d <$> fa)

-- | Default definition for 'closed' given that @p@ is 'Corepresentable'
closedCorep :: Corepresentable p => p a b -> p (x -> a) (x -> b)
closedCorep p = cotabulate $ \fs x -> cosieve p (fmap ($ x) fs)

instance Corepresentable (->) where
  type Corep (->) = Identity
  cotabulate f = f . Identity
  {-# INLINE cotabulate #-}

instance Functor w => Corepresentable (Cokleisli w) where
  type Corep (Cokleisli w) = w
  cotabulate = Cokleisli
  {-# INLINE cotabulate #-}

instance Corepresentable Tagged where
  type Corep Tagged = Proxy
  cotabulate f = Tagged (f Proxy)
  {-# INLINE cotabulate #-}

instance Functor f => Corepresentable (Costar f) where
  type Corep (Costar f) = f
  cotabulate = Costar
  {-# INLINE cotabulate #-}

-- | 'cotabulate' and 'cosieve' form two halves of an isomorphism.
--
-- This can be used with the combinators from the @lens@ package.
--
-- @'cotabulated' :: 'Corep' f p => 'Iso'' (f d -> c) (p d c)@
cotabulated :: (Corepresentable p, Corepresentable q) => Iso (Corep p d -> c) (Corep q d' -> c') (p d c) (q d' c')
cotabulated = dimap cotabulate (fmap cosieve)
{-# INLINE cotabulated #-}

--------------------------------------------------------------------------------
-- * Prep
--------------------------------------------------------------------------------

-- | @'Prep' -| 'Star' :: [Hask, Hask] -> Prof@
--
-- This gives rise to a monad in @Prof@, @('Star'.'Prep')@, and
-- a comonad in @[Hask,Hask]@ @('Prep'.'Star')@
--
-- 'Prep' has a polymorphic kind since @5.6@.

-- Prep :: (Type -> k -> Type) -> (k -> Type)
data Prep p a where
  Prep :: x -> p x a -> Prep p a

instance Profunctor p => Functor (Prep p) where
  fmap f (Prep x p) = Prep x (rmap f p)

instance (Applicative (Rep p), Representable p) => Applicative (Prep p) where
  pure a = Prep () $ tabulate $ const $ pure a
  Prep xf pf <*> Prep xa pa = Prep (xf,xa) (tabulate go) where
    go (xf',xa') = sieve pf xf' <*> sieve pa xa'

instance (Monad (Rep p), Representable p) => Monad (Prep p) where
  return a = Prep () $ tabulate $ const $ return a
  Prep xa pa >>= f = Prep xa $ tabulate $ sieve pa >=> \a -> case f a of
    Prep xb pb -> sieve pb xb

prepAdj :: (forall a. Prep p a -> g a) -> p :-> Star g
prepAdj k p = Star $ \x -> k (Prep x p)

unprepAdj :: (p :-> Star g) -> Prep p a -> g a
unprepAdj k (Prep x p) = runStar (k p) x

prepUnit :: p :-> Star (Prep p)
prepUnit p = Star $ \x -> Prep x p

prepCounit :: Prep (Star f) a -> f a
prepCounit (Prep x p) = runStar p x

--------------------------------------------------------------------------------
-- * Coprep
--------------------------------------------------------------------------------

-- | 'Prep' has a polymorphic kind since @5.6@.

-- Coprep :: (k -> Type -> Type) -> (k -> Type)
newtype Coprep p a = Coprep { runCoprep :: forall r. p a r -> r }

instance Profunctor p => Functor (Coprep p) where
  fmap f (Coprep g) = Coprep (g . lmap f)

-- | @'Coprep' -| 'Costar' :: [Hask, Hask]^op -> Prof@
--
-- Like all adjunctions this gives rise to a monad and a comonad.
--
-- This gives rise to a monad on Prof @('Costar'.'Coprep')@ and
-- a comonad on @[Hask, Hask]^op@ given by @('Coprep'.'Costar')@ which
-- is a monad in @[Hask,Hask]@
coprepAdj :: (forall a. f a -> Coprep p a) -> p :-> Costar f
coprepAdj k p = Costar $ \f -> runCoprep (k f) p

uncoprepAdj :: (p :-> Costar f) -> f a -> Coprep p a
uncoprepAdj k f = Coprep $ \p -> runCostar (k p) f

coprepUnit :: p :-> Costar (Coprep p)
coprepUnit p = Costar $ \f -> runCoprep f p

coprepCounit :: f a -> Coprep (Costar f) a
coprepCounit f = Coprep $ \p -> runCostar p f
