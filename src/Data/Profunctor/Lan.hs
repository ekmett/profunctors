{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE Safe #-}
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2011-2022 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  Rank2Types, TFs
--
----------------------------------------------------------------------------
module Data.Profunctor.Lan
  ( Lan(..)
  , decomposeLan
  , postcomposeLan
  , curryLan
  , uncurryLan
  ) where

import Control.Category
import Data.Profunctor
import Data.Profunctor.Composition
import Data.Profunctor.Functor
import Data.Profunctor.Monad
import Data.Profunctor.Unsafe
import Prelude hiding (id,(.))

--------------------------------------------------------------------------------
-- * Lan
--------------------------------------------------------------------------------

-- | This represents the left Kan extension of a 'Profunctor' @q@ along a
-- 'Profunctor' @p@ in a limited version of the 2-category of Profunctors where
-- the only object is the category Hask, 1-morphisms are profunctors composed
-- and compose with Profunctor composition, and 2-morphisms are just natural
-- transformations.
--
-- 'Lan' has a polymorphic kind.

-- Lan :: (k1 -> k2 -> Type) -> (k1 -> k3 -> Type) -> (k2 -> k3 -> Type)
newtype Lan p q a b = Lan { runLan :: forall y. p b y -> q a y }

instance Profunctor p => ProfunctorFunctor (Lan p) where
  promap f (Lan g) = Lan (f . g)

instance (Profunctor p, Category p) => ProfunctorComonad (Lan p) where
  proextract (Lan f) = f id
  produplicate (Lan f) = Lan $ \ p -> Lan $ \q -> f (q . p)

instance (Profunctor p, Profunctor q) => Profunctor (Lan p q) where
  dimap ca bd f = Lan (lmap ca . runLan f . lmap bd)
  {-# INLINE dimap #-}
  lmap ca f = Lan (lmap ca . runLan f)
  {-# INLINE lmap #-}
  rmap bd f = Lan (runLan f . lmap bd)
  {-# INLINE rmap #-}
  bd #. f = Lan (\p -> runLan f (p .# bd))
  {-# INLINE (#.) #-}
  f .# ca = Lan (\p -> runLan f p .# ca)
  {-# INLINE (.#) #-}

instance Profunctor p => Functor (Lan p q a) where
  fmap bd f = Lan (runLan f . lmap bd)
  {-# INLINE fmap #-}

-- | @'Lan' p p@ forms a 'Monad' in the 'Profunctor' 2-category, which is isomorphic to a Haskell 'Category' instance.
instance p ~ q => Category (Lan p q) where
  id = Lan id
  {-# INLINE id #-}
  Lan f . Lan g = Lan (g . f)
  {-# INLINE (.) #-}

-- | With `postcomposeLan`, the 2-morphism that defines a left Kan extension.
decomposeLan :: Procompose p (Lan p q) :-> q
decomposeLan (Procompose p (Lan pq)) = pq p
{-# INLINE decomposeLan #-}

-- | With `decomposeLan`, the 2-morphism that defines a left Kan extension.
postcomposeLan :: Profunctor q => Procompose (Lan p (->)) q :-> Lan p q
postcomposeLan (Procompose pf q) = Lan (\pyb -> runLan pf pyb `rmap` q)
{-# INLINE postcomposeLan #-}

curryLan :: (Procompose p q :-> r) -> q :-> Lan p r
curryLan f q = Lan $ \p -> f (Procompose p q)
{-# INLINE curryLan #-}

uncurryLan :: (q :-> Lan p r) -> Procompose p q :-> r
uncurryLan f (Procompose p q) = runLan (f q) p
{-# INLINE uncurryLan #-}
