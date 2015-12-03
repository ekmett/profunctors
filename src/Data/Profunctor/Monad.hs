{-# LANGUAGE CPP #-}
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
import Data.Profunctor.Types

class ProfunctorFunctor t where
  promap    :: Profunctor p => (p :-> q) -> t p :-> t q

instance Functor f => ProfunctorFunctor (Tannen f) where
  promap f (Tannen g) = Tannen (fmap f g)

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

class ProfunctorFunctor t => ProfunctorComonad t where
  proextract :: Profunctor p => t p :-> p
  produplicate :: Profunctor p => t p :-> t (t p)

instance Comonad f => ProfunctorComonad (Tannen f) where
  proextract = extract . runTannen
  produplicate (Tannen w) = Tannen $ extend Tannen w

