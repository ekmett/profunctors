{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Safe #-}

-- |
-- Copyright   :  (C) 2015-2021 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable, MPTCs, fundeps

module Data.Profunctor.Adjunction 
( ProfunctorAdjunction(..)
) where

import Data.Profunctor.Types
import Data.Profunctor.Functor

-- | Laws:
--
-- @
-- 'unit' '.' 'counit' ≡ 'id'
-- 'counit' '.' 'unit' ≡ 'id'
-- @

class (ProfunctorFunctor f, ProfunctorFunctor u) => ProfunctorAdjunction f u | f -> u, u -> f where
  unit   :: Profunctor p => p :-> u (f p)
  counit :: Profunctor p => f (u p) :-> p
