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
module Data.Profunctor.Functor where

import Data.Bifunctor.Tannen
import Data.Bifunctor.Product
import Data.Bifunctor.Sum
import Data.Profunctor.Types

-- | 'ProfunctorFunctor' has a polymorphic kind since @5.6@.
-- 'ProfunctorFunctor' has a quanitified superclass since @6@.
--
-- ProfunctorFunctor :: ((Type -> Type -> Type) -> (Type -> Type -> Type)) -> Constraint
class (forall p. Profunctor p => Profunctor (t p)) => ProfunctorFunctor t where
  -- | Laws:
  --
  -- @
  -- 'promap' f '.' 'promap' g ≡ 'promap' (f '.' g)
  -- 'promap' 'id' ≡ 'id'
  -- @
  promap :: Profunctor p => (p :-> q) -> t p :-> t q

instance Functor f => ProfunctorFunctor (Tannen f) where
  promap f (Tannen g) = Tannen (fmap f g)

instance Profunctor p => ProfunctorFunctor (Product p) where
  promap f (Pair p q) = Pair p (f q)

instance Profunctor p => ProfunctorFunctor (Sum p) where
  promap _ (L2 p) = L2 p
  promap f (R2 q) = R2 (f q)
