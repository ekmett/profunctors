module Data.Profunctor.Monad where

import Data.Profunctor

class ProfunctorMonad t where
  proreturn :: Profunctor p => p a b -> t p a b
  projoin   :: Profunctor p => t (t p) a b -> t p a b

class ProfunctorComonad t where
  proextract :: Profunctor p => t p a b -> p a b
  produplicate :: Profunctor p => t p a b -> t (t p) a b
