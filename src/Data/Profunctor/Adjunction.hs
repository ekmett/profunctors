{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes #-}
module Data.Profunctor.Adjunction where

import Data.Profunctor

class f -| u | f -> u, u -> f where
  unit   :: Profunctor p => p -/-> u (f p)
  counit :: Profunctor p => f (u p) -/-> p
