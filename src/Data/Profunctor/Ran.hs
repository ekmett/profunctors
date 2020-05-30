{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2013-2015 Edward Kmett and Dan Doel
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  Rank2Types, TFs
--
----------------------------------------------------------------------------
module Data.Profunctor.Ran
  ( Ran(..)
  , decomposeRan
  , precomposeRan
  , curryRan
  , uncurryRan
  , Codensity(..)
  , decomposeCodensity
  ) where

import Control.Category
import Data.Profunctor
import Data.Profunctor.Composition
import Data.Profunctor.Monad
import Data.Profunctor.Unsafe
import Prelude hiding (id,(.))

--------------------------------------------------------------------------------
-- * Ran
--------------------------------------------------------------------------------

-- | This represents the right Kan extension of a 'Profunctor' @q@ along a
-- 'Profunctor' @p@ in a limited version of the 2-category of Profunctors where
-- the only object is the category Hask, 1-morphisms are profunctors composed
-- and compose with Profunctor composition, and 2-morphisms are just natural
-- transformations.
--
-- 'Ran' has a polymorphic kind since @5.6@.

-- Ran :: (k1 -> k2 -> Type) -> (k1 -> k3 -> Type) -> (k2 -> k3 -> Type)
newtype Ran p q a b = Ran { runRan :: forall x. p x a -> q x b }

instance ProfunctorFunctor (Ran p) where
  promap f (Ran g) = Ran (f . g)

instance Category p => ProfunctorComonad (Ran p) where
  proextract (Ran f) = f id
  produplicate (Ran f) = Ran $ \ p -> Ran $ \q -> f (p . q)

instance (Profunctor p, Profunctor q) => Profunctor (Ran p q) where
  dimap ca bd f = Ran (rmap bd . runRan f . rmap ca)
  {-# INLINE dimap #-}
  lmap ca f = Ran (runRan f . rmap ca)
  {-# INLINE lmap #-}
  rmap bd f = Ran (rmap bd . runRan f)
  {-# INLINE rmap #-}
  bd #. f = Ran (\p -> bd #. runRan f p)
  {-# INLINE (#.) #-}
  f .# ca = Ran (\p -> runRan f (ca #. p))
  {-# INLINE (.#) #-}

instance Profunctor q => Functor (Ran p q a) where
  fmap bd f = Ran (rmap bd . runRan f)
  {-# INLINE fmap #-}

-- | @'Ran' p p@ forms a 'Monad' in the 'Profunctor' 2-category, which is isomorphic to a Haskell 'Category' instance.
instance p ~ q => Category (Ran p q) where
  id = Ran id
  {-# INLINE id #-}
  Ran f . Ran g = Ran (f . g)
  {-# INLINE (.) #-}

-- | The 2-morphism that defines a right Kan extension.
--
-- Note: When @q@ is left adjoint to @'Ran' q (->)@ then 'decomposeRan' is the 'counit' of the adjunction.
decomposeRan :: Procompose (Ran q p) q :-> p
decomposeRan (Procompose (Ran qp) q) = qp q
{-# INLINE decomposeRan #-}

precomposeRan :: Profunctor q => Procompose q (Ran p (->)) :-> Ran p q
precomposeRan (Procompose p pf) = Ran (\pxa -> runRan pf pxa `lmap` p)
{-# INLINE precomposeRan #-}

curryRan :: (Procompose p q :-> r) -> p :-> Ran q r
curryRan f p = Ran $ \q -> f (Procompose p q)
{-# INLINE curryRan #-}

uncurryRan :: (p :-> Ran q r) -> Procompose p q :-> r
uncurryRan f (Procompose p q) = runRan (f p) q
{-# INLINE uncurryRan #-}

--------------------------------------------------------------------------------
-- * Codensity
--------------------------------------------------------------------------------

-- | This represents the right Kan extension of a 'Profunctor' @p@ along
-- itself. This provides a generalization of the \"difference list\" trick to
-- profunctors.
--
-- 'Codensity' has a polymorphic kind since @5.6@.

-- Codensity :: (k1 -> k2 -> Type) -> (k2 -> k2 -> Type)
newtype Codensity p a b = Codensity { runCodensity :: forall x. p x a -> p x b }

instance Profunctor p => Profunctor (Codensity p) where
  dimap ca bd f = Codensity (rmap bd . runCodensity f . rmap ca)
  {-# INLINE dimap #-}
  lmap ca f = Codensity (runCodensity f . rmap ca)
  {-# INLINE lmap #-}
  rmap bd f = Codensity (rmap bd . runCodensity f)
  {-# INLINE rmap #-}
  bd #. f = Codensity (\p -> bd #. runCodensity f p)
  {-# INLINE (#.) #-}
  f .# ca = Codensity (\p -> runCodensity f (ca #. p))
  {-# INLINE (.#) #-}

instance Profunctor p => Functor (Codensity p a) where
  fmap bd f = Codensity (rmap bd . runCodensity f)
  {-# INLINE fmap #-}

instance Category (Codensity p) where
  id = Codensity id
  {-# INLINE id #-}
  Codensity f . Codensity g = Codensity (f . g)
  {-# INLINE (.) #-}

decomposeCodensity :: Procompose (Codensity p) p a b -> p a b
decomposeCodensity (Procompose (Codensity pp) p) = pp p
{-# INLINE decomposeCodensity #-}
