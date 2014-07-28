{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Data.Profunctor.Monad where

import Data.Profunctor

class ProfunctorMonad t where
  proreturn :: Profunctor p => p -/-> t p
  projoin   :: Profunctor p => t (t p) -/-> t p

class ProfunctorComonad t where
  proextract :: Profunctor p => t p -/-> p
  produplicate :: Profunctor p => t p -/-> t (t p)
