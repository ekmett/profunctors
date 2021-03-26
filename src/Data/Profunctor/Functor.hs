{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE ExplicitNamespaces #-}

-- |
-- Copyright   :  (C) 2014-2021 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  portable

module Data.Profunctor.Functor 
( type (:->)
, ProfunctorFunctor(..)
) where

import Data.Bifunctor.Functor ((:->))
import Data.Profunctor.Internal
