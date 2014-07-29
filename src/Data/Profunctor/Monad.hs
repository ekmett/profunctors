{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Data.Profunctor.Monad where

import Data.Profunctor

class ProfunctorFunctor t where
  promap    :: Profunctor p => (p :-> q) -> t p :-> t q

class ProfunctorFunctor t => ProfunctorMonad t where
  proreturn :: Profunctor p => p :-> t p
  projoin   :: Profunctor p => t (t p) :-> t p

class ProfunctorFunctor t => ProfunctorComonad t where
  proextract :: Profunctor p => t p :-> p
  produplicate :: Profunctor p => t p :-> t (t p)
