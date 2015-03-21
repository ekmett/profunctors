{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ >= 702 && __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE Trustworthy #-}
#endif
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
    Sieve(..)
  , Representable(..)
  , tabulated
  , firstRep, secondRep
  -- * Corepresentable Profunctors
  , Cosieve(..)
  , Corepresentable(..)
  , cotabulated
  ) where

import Control.Applicative
import Control.Arrow
import Control.Comonad
import Data.Functor.Identity
import Data.Profunctor
import Data.Proxy
import Data.Tagged

-- | A 'Profunctor' @p@ is a 'Sieve' on 'f' if it is a subprofunctor of 'Star f'.
class (Profunctor p, Functor f) => Sieve p f | p -> f where
  sieve :: p a b -> a -> f b

instance Sieve (->) Identity where
  sieve f = Identity . f
  {-# INLINE sieve #-}

instance (Monad m, Functor m) => Sieve (Kleisli m) m where
  sieve = runKleisli
  {-# INLINE sieve #-}

instance Functor f => Sieve (Star f) f where
  sieve = runStar
  {-# INLINE sieve #-}

instance Sieve (Forget r) (Const r) where
  sieve = (Const .) . runForget
  {-# INLINE sieve #-}

-- * Representable Profunctors

-- | A 'Profunctor' @p@ is 'Representable' if there exists a 'Functor' @f@ such that
-- @p d c@ is isomorphic to @d -> f c@.
class (Sieve p (Rep p), Strong p) => Representable p where
  type Rep p :: * -> *
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

type Iso s t a b = forall p f. (Profunctor p, Functor f) => p a (f b) -> p s (f t)

-- | 'tabulate' and 'sieve' form two halves of an isomorphism.
--
-- This can be used with the combinators from the @lens@ package.
--
-- @'tabulated' :: 'Representable' p => 'Iso'' (d -> 'Rep' p c) (p d c)@
tabulated :: (Representable p, Representable q) => Iso (d -> Rep p c) (d' -> Rep q c') (p d c) (q d' c')
tabulated = dimap tabulate (fmap sieve)
{-# INLINE tabulated #-}

class (Profunctor p, Functor f) => Cosieve p f | p -> f where
  cosieve :: p a b -> f a -> b

instance Cosieve (->) Identity where
  cosieve f (Identity d) = f d
  {-# INLINE cosieve #-}

instance Functor w => Cosieve (Cokleisli w) w where
  cosieve = runCokleisli
  {-# INLINE cosieve #-}

instance Cosieve Tagged Proxy where
  cosieve (Tagged a) _ = a
  {-# INLINE cosieve #-}

instance Functor f => Cosieve (Costar f) f where
  cosieve = runCostar
  {-# INLINE cosieve #-}

-- * Corepresentable Profunctors

-- | A 'Profunctor' @p@ is 'Corepresentable' if there exists a 'Functor' @f@ such that
-- @p d c@ is isomorphic to @f d -> c@.
class Cosieve p (Corep p) => Corepresentable p where
  type Corep p :: * -> *
  cotabulate :: (Corep p d -> c) -> p d c

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
