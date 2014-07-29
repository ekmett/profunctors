{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoImplicitPrelude #-}
module Data.Profunctor.Monoid where

import Control.Category
import Data.Profunctor
import Data.Profunctor.Composition

-- | a 'Category' that is also a 'Profunctor' is a 'Monoid' in @Prof@

eta :: (Profunctor p, Category p) => (->) :-> p
eta f = rmap f id

mu :: Category p => Procompose p p :-> p
mu (Procompose f g) = f . g
