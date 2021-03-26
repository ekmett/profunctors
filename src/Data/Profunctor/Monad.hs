{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE Safe #-}
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
import Data.Profunctor.Functor
import Data.Profunctor.Unsafe

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

instance Monad f => ProfunctorMonad (Tannen f) where
  proreturn = Tannen . return
  projoin (Tannen m) = Tannen $ m >>= runTannen

instance Profunctor p => ProfunctorMonad (Sum p) where
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

instance Profunctor p => ProfunctorComonad (Product p) where
  proextract (Pair _ q) = q
  produplicate pq@(Pair p _) = Pair p pq
