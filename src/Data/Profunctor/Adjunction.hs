{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes #-}
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2015 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable, MPTCs, fundeps
--
----------------------------------------------------------------------------
module Data.Profunctor.Adjunction where

import Data.Profunctor.Types
import Data.Profunctor.Monad

-- | Laws:
--
-- @
-- 'unit' '.' 'counit' ≡ 'id'
-- 'counit' '.' 'unit' ≡ 'id'
-- @

-- ProfunctorAdjunction :: ((Type -> Type -> Type) -> (Type -> Type -> Type)) -> ((Type -> Type -> Type) -> (Type -> Type -> Type)) -> Constraint
class (ProfunctorFunctor f, ProfunctorFunctor u) => ProfunctorAdjunction f u | f -> u, u -> f where
  unit   :: Profunctor p => p :-> u (f p)
  counit :: Profunctor p => f (u p) :-> p
