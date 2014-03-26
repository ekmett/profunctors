{-# LANGUAGE CPP #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2013 Edward Kmett and Dan Doel
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  Rank2Types, TFs
--
----------------------------------------------------------------------------
module Data.Profunctor.Rift
  ( Rift(..)
  , decomposeRift
  , precomposeRift
  ) where

import Control.Category
import Data.Profunctor.Unsafe
import Data.Profunctor.Composition
import Prelude hiding (id,(.))

-- | This represents the right Kan lift of a 'Profunctor' @q@ along a 'Profunctor' @p@ in a limited version of the 2-category of Profunctors where the only object is the category Hask, 1-morphisms are profunctors composed and compose with Profunctor composition, and 2-morphisms are just natural transformations.
newtype Rift p q a b = Rift { runRift :: forall x. p x a -> q x b }

--  Ran f g a = forall b. (a -> f b) -> g b

instance (Profunctor p, Profunctor q) => Profunctor (Rift p q) where
  dimap ca bd f = Rift (rmap bd . runRift f . rmap ca)
  {-# INLINE dimap #-}
  lmap ca f = Rift (runRift f . rmap ca)
  {-# INLINE lmap #-}
  rmap bd f = Rift (rmap bd . runRift f)
  {-# INLINE rmap #-}
  bd #. f = Rift (\p -> bd #. runRift f p)
  {-# INLINE ( #. ) #-}
  f .# ca = Rift (\p -> runRift f (ca #. p))
  {-# INLINE (.#) #-}

instance Profunctor q => Functor (Rift p q a) where
  fmap bd f = Rift (rmap bd . runRift f)
  {-# INLINE fmap #-}

-- | @'Rift' p p@ forms a 'Monad' in the 'Profunctor' 2-category, which is isomorphic to a Haskell 'Category' instance.
instance p ~ q => Category (Rift p q) where
  id = Rift id
  {-# INLINE id #-}
  Rift f . Rift g = Rift (f . g)
  {-# INLINE (.) #-}

-- | The 2-morphism that defines a right Kan lift.
--
-- Note: When @q@ is left adjoint to @'Rift' q (->)@ then 'decomposeRift' is the 'counit' of the adjunction.
decomposeRift :: Procompose q (Rift q p) a b -> p a b
decomposeRift (Procompose q (Rift qp)) = qp q
{-# INLINE decomposeRift #-}

precomposeRift :: Profunctor q => Procompose (Rift p (->)) q a b -> Rift p q a b
precomposeRift (Procompose pf p) = Rift (\pxa -> runRift pf pxa `lmap` p)
{-# INLINE precomposeRift #-}
