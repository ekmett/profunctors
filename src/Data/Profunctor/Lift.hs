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
module Data.Profunctor.Lift
  ( Lift(..)
  , decomposeLift
--  , precomposeLift
  ) where

import Control.Category
import Data.Profunctor.Unsafe
import Data.Profunctor.Composition
import Prelude hiding (id,(.))

-- | This represents the left Kan lift of a 'Profunctor' @q@ along a 'Profunctor' @p@ in a limited version of the 2-category of Profunctors where the only object is the category Hask, 1-morphisms are profunctors composed and compose with Profunctor composition, and 2-morphisms are just natural transformations.
newtype Lift p q a b = Lift { runLift :: forall x. p b x -> q a x }


instance (Profunctor p, Profunctor q) => Profunctor (Lift p q) where
  dimap ca bd f = Lift (lmap ca . runLift f . lmap bd)
  {-# INLINE dimap #-}
  lmap ca f = Lift (lmap ca . runLift f)
  {-# INLINE lmap #-}
  rmap bd f = Lift (runLift f . lmap bd)
  {-# INLINE rmap #-}
  bd #. f = Lift (\p -> runLift f (p .# bd))
  {-# INLINE ( #. ) #-}
  f .# ca = Lift (\p -> runLift f p .# ca)
  {-# INLINE (.#) #-}

instance Profunctor p => Functor (Lift p q a) where
  fmap bd f = Lift (runLift f . lmap bd)
  {-# INLINE fmap #-}

-- | @'Lift' p p@ forms a 'Monad' in the 'Profunctor' 2-category, which is isomorphic to a Haskell 'Category' instance.
instance p ~ q => Category (Lift p q) where
  id = Lift id
  {-# INLINE id #-}
  Lift f . Lift g = Lift (g . f)
  {-# INLINE (.) #-}

-- | The 2-morphism that defines a left Kan lift.
--
-- Note: When @p@ is left adjoint to @'Lift' p (->)@ then 'decomposeLift' is the 'counit' of the adjunction.
decomposeLift :: Procompose (Lift p q) p a b -> q a b
decomposeLift (Procompose (Lift pq) p) = pq p
{-# INLINE decomposeLift #-}

{-
precomposeLift :: Profunctor q => Procompose (Lift p (->)) q a b -> Lift p q a b
precomposeLift (Procompose pf p) = Lift (\pxa -> runLift pf pxa `lmap` p)
{-# INLINE precomposeLift #-}
-}
