{-# LANGUAGE CPP #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
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
module Data.Profunctor.Monad where

import Control.Comonad
import Data.Bifunctor.Tannen
import Data.Bifunctor.Product
import Data.Bifunctor.Sum
import Data.Profunctor.Types

-- | 'ProfunctorFunctor' has a polymorphic kind since @5.6@.

-- ProfunctorFunctor :: ((Type -> Type -> Type) -> (k1 -> k2 -> Type)) -> Constraint
class ProfunctorFunctor t where
  -- | Laws:
  --
  -- @
  -- 'promap' f '.' 'promap' g ≡ 'promap' (f '.' g)
  -- 'promap' 'id' ≡ 'id'
  -- @
  promap :: Profunctor p => (p :-> q) -> t p :-> t q

instance Functor f => ProfunctorFunctor (Tannen f) where
  promap f (Tannen g) = Tannen (fmap f g)

instance ProfunctorFunctor (Product p) where
  promap f (Pair p q) = Pair p (f q)

instance ProfunctorFunctor (Sum p) where
  promap _ (L2 p) = L2 p
  promap f (R2 q) = R2 (f q)

-- | Laws:
--
-- @
-- 'promap' f '.' 'proreturn' ≡ 'proreturn' '.' f
-- 'projoin' '.' 'proreturn' ≡ 'id'
-- 'projoin' '.' 'promap' 'proreturn' ≡ 'id'
-- 'projoin' '.' 'projoin' ≡ 'projoin' '.' 'promap' 'projoin'
-- @

-- ProfunctorMonad :: ((Type -> Type -> Type) -> (Type -> Type -> Type)) -> Constraint
class ProfunctorFunctor t => ProfunctorMonad t where
  proreturn :: Profunctor p => p :-> t p
  projoin   :: Profunctor p => t (t p) :-> t p

#if __GLASGOW_HASKELL__ < 710
instance (Functor f, Monad f) => ProfunctorMonad (Tannen f) where
#else
instance Monad f => ProfunctorMonad (Tannen f) where
#endif
  proreturn = Tannen . return
  projoin (Tannen m) = Tannen $ m >>= runTannen

instance ProfunctorMonad (Sum p) where
  proreturn = R2
  projoin (L2 p) = L2 p
  projoin (R2 m) = m

-- | Laws:
--
-- @
-- 'proextract' '.' 'promap' f ≡ f '.' 'proextract'
-- 'proextract' '.' 'produplicate' ≡ 'id'
-- 'promap' 'proextract' '.' 'produplicate' ≡ 'id'
-- 'produplicate' '.' 'produplicate' ≡ 'promap' 'produplicate' '.' 'produplicate'
-- @

-- ProfunctorComonad :: ((Type -> Type -> Type) -> (Type -> Type -> Type)) -> Constraint
class ProfunctorFunctor t => ProfunctorComonad t where
  proextract :: Profunctor p => t p :-> p
  produplicate :: Profunctor p => t p :-> t (t p)

instance Comonad f => ProfunctorComonad (Tannen f) where
  proextract = extract . runTannen
  produplicate (Tannen w) = Tannen $ extend Tannen w

instance ProfunctorComonad (Product p) where
  proextract (Pair _ q) = q
  produplicate pq@(Pair p _) = Pair p pq
