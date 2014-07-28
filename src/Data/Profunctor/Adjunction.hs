{-# LANGUAGE TypeOperators, MultiParamTypeClasses, FunctionalDependencies #-}
module Data.Profunctor.Adjunction where

import Data.Profunctor

class f -| u | f -> u, u -> f where
  unit   :: Profunctor p => p a b -> u (f p) a b
  counit :: Profunctor p => f (u p) a b -> p a b
