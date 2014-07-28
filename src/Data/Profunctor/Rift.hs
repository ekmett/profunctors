{-# LANGUAGE CPP #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
module Data.Profunctor.Rift
  ( Rift(..)
  , decomposeRift
  ) where

import Control.Category
import Data.Profunctor
import Data.Profunctor.Adjunction
import Data.Profunctor.Composition
import Data.Profunctor.Monad
import Data.Profunctor.Unsafe
import Prelude hiding (id,(.))

-- | This represents the right Kan lift of a 'Profunctor' @q@ along a 'Profunctor' @p@ in a limited version of the 2-category of Profunctors where the only object is the category Hask, 1-morphisms are profunctors composed and compose with Profunctor composition, and 2-morphisms are just natural transformations.
newtype Rift p q a b = Rift { runRift :: forall x. p b x -> q a x }

instance Category p => ProfunctorComonad (Rift p) where
  proextract (Rift f) = f id
  produplicate (Rift f) = Rift $ \p -> Rift $ \q -> f (q . p)

instance (Profunctor p, Profunctor q) => Profunctor (Rift p q) where
  dimap ca bd f = Rift (lmap ca . runRift f . lmap bd)
  {-# INLINE dimap #-}
  lmap ca f = Rift (lmap ca . runRift f)
  {-# INLINE lmap #-}
  rmap bd f = Rift (runRift f . lmap bd)
  {-# INLINE rmap #-}
  bd #. f = Rift (\p -> runRift f (p .# bd))
  {-# INLINE ( #. ) #-}
  f .# ca = Rift (\p -> runRift f p .# ca)
  {-# INLINE (.#) #-}

instance Profunctor p => Functor (Rift p q a) where
  fmap bd f = Rift (runRift f . lmap bd)
  {-# INLINE fmap #-}

-- | @'Rift' p p@ forms a 'Monad' in the 'Profunctor' 2-category, which is isomorphic to a Haskell 'Category' instance.
instance p ~ q => Category (Rift p q) where
  id = Rift id
  {-# INLINE id #-}
  Rift f . Rift g = Rift (g . f)
  {-# INLINE (.) #-}

-- | The 2-morphism that defines a left Kan lift.
--
-- Note: When @p@ is right adjoint to @'Rift' p (->)@ then 'decomposeRift' is the 'counit' of the adjunction.
decomposeRift :: Procompose p (Rift p q) -/-> q
decomposeRift (Procompose p (Rift pq)) = pq p
{-# INLINE decomposeRift #-}

instance Procompose p -| Rift p where
  counit (Procompose p (Rift pq)) = pq p
  unit q = Rift $ \p -> Procompose p q
