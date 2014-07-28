{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DefaultSignatures #-}
module Data.Profunctor.Monoid where

import Control.Category
import Control.Comonad
import Control.Arrow
import Data.Profunctor
import Data.Profunctor.Closed
import Data.Profunctor.Composition
import Prelude hiding ((.),id)

class ProfunctorMonoid p where
  eta :: (->) -/-> p
  mu  :: Procompose p p -/-> p
  default mu :: Category p => Procompose p p -/-> p
  mu (Procompose f g) = f . g

instance ProfunctorMonoid (->) where
  eta = id
  mu (Procompose f g) = f . g

instance Monad m => ProfunctorMonoid (Kleisli m) where
  eta = arr
  mu (Procompose f g) = f . g

instance Comonad w => ProfunctorMonoid (Cokleisli w) where
  eta = arr
  mu (Procompose f g) = f . g

instance (Closed p, ProfunctorMonoid p) => ProfunctorMonoid (Closure p) where
  eta p = Closure $ eta (closed p)
  mu (Procompose (Closure f) (Closure g)) = Closure $ mu (Procompose f g)
