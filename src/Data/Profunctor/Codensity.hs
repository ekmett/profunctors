{-# LANGUAGE CPP #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2014 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  Rank2Types, TFs
--
----------------------------------------------------------------------------
module Data.Profunctor.Codensity
  ( Codensity(..)
  , decomposeCodensity
  ) where

import Control.Category
import Data.Profunctor.Unsafe
import Data.Profunctor.Composition
import Prelude hiding (id,(.))

-- | This represents the right Kan extension of a 'Profunctor' @p@ along itself. This provides a generalization of the \"difference list\" trick to profunctors.
newtype Codensity p a b = Codensity { runCodensity :: forall x. p x a -> p x b }

instance Profunctor p => Profunctor (Codensity p) where
  dimap ca bd f = Codensity (rmap bd . runCodensity f . rmap ca)
  {-# INLINE dimap #-}
  lmap ca f = Codensity (runCodensity f . rmap ca)
  {-# INLINE lmap #-}
  rmap bd f = Codensity (rmap bd . runCodensity f)
  {-# INLINE rmap #-}
  bd #. f = Codensity (\p -> bd #. runCodensity f p)
  {-# INLINE ( #. ) #-}
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
