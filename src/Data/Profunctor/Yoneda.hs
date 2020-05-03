{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Trustworthy #-}
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2017 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  Rank2Types, TFs
--
----------------------------------------------------------------------------
module Data.Profunctor.Yoneda
  ( Yoneda(..), extractYoneda, duplicateYoneda
  , Coyoneda(..), returnCoyoneda, joinCoyoneda
  ) where

import Control.Category
import Data.Coerce (Coercible, coerce)
import Data.Profunctor
import Data.Profunctor.Monad
import Data.Profunctor.Traversing
import Data.Profunctor.Unsafe
import Prelude hiding (id,(.))

--------------------------------------------------------------------------------
-- * Yoneda
--------------------------------------------------------------------------------

-- | This is the cofree profunctor given a data constructor of kind @* -> * -> *@
newtype Yoneda p a b = Yoneda { runYoneda :: forall x y. (x -> a) -> (b -> y) -> p x y }

-- Yoneda is a comonad on |*| -> Nat(|*|,*), we don't need the profunctor constraint to extract or duplicate
-- |
-- @
-- 'projoin' '.' 'extractYoneda' ≡ 'id'
-- 'extractYoneda' '.' 'projoin' ≡ 'id'
-- 'projoin' ≡ 'extractYoneda'
-- @
extractYoneda :: Yoneda p a b -> p a b
extractYoneda p = runYoneda p id id

-- |
-- @
-- 'projoin' '.' 'duplicateYoneda' ≡ 'id'
-- 'duplicateYoneda' '.' 'projoin' ≡ 'id'
-- 'duplicateYoneda' = 'proreturn'
-- @
duplicateYoneda :: Yoneda p a b -> Yoneda (Yoneda p) a b
duplicateYoneda p = Yoneda $ \l r -> dimap l r p

instance Profunctor (Yoneda p) where
  dimap l r p = Yoneda $ \l' r' -> runYoneda p (l . l') (r' . r)
  {-# INLINE dimap #-}
  lmap l p = Yoneda $ \l' r -> runYoneda p (l . l') r
  {-# INLINE lmap #-}
  rmap r p = Yoneda $ \l r' -> runYoneda p l (r' . r)
  {-# INLINE rmap #-}
  (.#) p _ = coerce p
  {-# INLINE (.#) #-}
  (#.) _ = coerce (\x -> x :: b) :: forall a b. Coercible b a => a -> b
  {-# INLINE (#.) #-}

instance Functor (Yoneda p a) where
  fmap f p = Yoneda $ \l r -> runYoneda p l (r . f)
  {-# INLINE fmap #-}

instance ProfunctorFunctor Yoneda where
  promap f p = Yoneda $ \l r -> f (runYoneda p l r)
  {-# INLINE promap #-}

instance ProfunctorComonad Yoneda where
  proextract p = runYoneda p id id
  {-# INLINE proextract #-}
  produplicate p = Yoneda $ \l r -> dimap l r p
  {-# INLINE produplicate #-}

instance ProfunctorMonad Yoneda where
  proreturn p = Yoneda $ \l r -> dimap l r p
  {-# INLINE proreturn #-}
  projoin p = runYoneda p id id
  {-# INLINE projoin #-}

instance (Category p, Profunctor p) => Category (Yoneda p) where
  id = Yoneda $ \l r -> dimap l r id
  {-# INLINE id #-}
  p . q = Yoneda $ \ l r -> runYoneda p id r . runYoneda q l id
  {-# INLINE (.) #-}

instance Strong p => Strong (Yoneda p) where
  first' = proreturn . first' . extractYoneda
  {-# INLINE first' #-}
  second' = proreturn . second' . extractYoneda
  {-# INLINE second' #-}

instance Choice p => Choice (Yoneda p) where
  left' = proreturn . left' . extractYoneda
  {-# INLINE left' #-}
  right' = proreturn . right' . extractYoneda
  {-# INLINE right' #-}

instance Costrong p => Costrong (Yoneda p) where
  unfirst = proreturn . unfirst . extractYoneda
  {-# INLINE unfirst #-}
  unsecond = proreturn . unsecond . extractYoneda
  {-# INLINE unsecond #-}

instance Cochoice p => Cochoice (Yoneda p) where
  unleft = proreturn . unleft . extractYoneda
  {-# INLINE unleft #-}
  unright = proreturn . unright . extractYoneda
  {-# INLINE unright #-}

instance Closed p => Closed (Yoneda p) where
  closed = proreturn . closed . extractYoneda
  {-# INLINE closed #-}

instance Mapping p => Mapping (Yoneda p) where
  map' = proreturn . map' . extractYoneda
  {-# INLINE map' #-}

instance Traversing p => Traversing (Yoneda p) where
  traverse' = proreturn . traverse' . extractYoneda
  {-# INLINE traverse' #-}
  wander f = proreturn . wander f . extractYoneda
  {-# INLINE wander #-}

--------------------------------------------------------------------------------
-- * Coyoneda
--------------------------------------------------------------------------------

data Coyoneda p a b where
  Coyoneda :: (a -> x) -> (y -> b) -> p x y -> Coyoneda p a b

-- Coyoneda is a Monad on |*| -> Nat(|*|,*), we don't need the profunctor constraint to extract or duplicate

-- |
-- @
-- 'returnCoyoneda' '.' 'proextract' ≡ 'id'
-- 'proextract' '.' 'returnCoyoneda' ≡ 'id'
-- 'produplicate' ≡ 'returnCoyoneda'
-- @
returnCoyoneda :: p a b -> Coyoneda p a b
returnCoyoneda = Coyoneda id id

-- |
-- @
-- 'joinCoyoneda' '.' 'produplicate' ≡ 'id'
-- 'produplicate' '.' 'joinCoyoneda' ≡ 'id'
-- 'joinCoyoneda' ≡ 'proextract'
-- @
joinCoyoneda :: Coyoneda (Coyoneda p) a b -> Coyoneda p a b
joinCoyoneda (Coyoneda l r p) = dimap l r p

instance Profunctor (Coyoneda p) where
  dimap l r (Coyoneda l' r' p) = Coyoneda (l' . l) (r . r') p
  {-# INLINE dimap #-}
  lmap l (Coyoneda l' r p) = Coyoneda (l' . l) r p
  {-# INLINE lmap #-}
  rmap r (Coyoneda l r' p) = Coyoneda l (r . r') p
  {-# INLINE rmap #-}
  (.#) p _ = coerce p
  {-# INLINE (.#) #-}
  (#.) _ = coerce (\x -> x :: b) :: forall a b. Coercible b a => a -> b
  {-# INLINE (#.) #-}

instance ProfunctorFunctor Coyoneda where
  promap f (Coyoneda l r p) = Coyoneda l r (f p)
  {-# INLINE promap #-}

instance ProfunctorComonad Coyoneda where
  proextract (Coyoneda l r p) = dimap l r p
  {-# INLINE proextract #-}
  produplicate = Coyoneda id id
  {-# INLINE produplicate #-}

instance ProfunctorMonad Coyoneda where
  proreturn = returnCoyoneda
  {-# INLINE proreturn #-}
  projoin = joinCoyoneda
  {-# INLINE projoin #-}

instance (Category p, Profunctor p) => Category (Coyoneda p) where
  id = Coyoneda id id id
  {-# INLINE id #-}
  Coyoneda lp rp p . Coyoneda lq rq q = Coyoneda lq rp (p . rmap (lp . rq) q)
  {-# INLINE (.) #-}

instance Strong p => Strong (Coyoneda p) where
  first' = returnCoyoneda . first' . proextract
  {-# INLINE first' #-}
  second' = returnCoyoneda . second' . proextract
  {-# INLINE second' #-}

instance Choice p => Choice (Coyoneda p) where
  left' = returnCoyoneda . left' . proextract
  {-# INLINE left' #-}
  right' = returnCoyoneda . right' . proextract
  {-# INLINE right' #-}

instance Costrong p => Costrong (Coyoneda p) where
  unfirst = returnCoyoneda . unfirst . proextract
  {-# INLINE unfirst #-}
  unsecond = returnCoyoneda . unsecond . proextract
  {-# INLINE unsecond #-}

instance Cochoice p => Cochoice (Coyoneda p) where
  unleft = returnCoyoneda . unleft . proextract
  {-# INLINE unleft #-}
  unright = returnCoyoneda . unright . proextract
  {-# INLINE unright #-}

instance Closed p => Closed (Coyoneda p) where
  closed = returnCoyoneda . closed . proextract
  {-# INLINE closed #-}

instance Mapping p => Mapping (Coyoneda p) where
  map' = returnCoyoneda . map' . proextract
  {-# INLINE map' #-}

instance Traversing p => Traversing (Coyoneda p) where
  traverse' = returnCoyoneda . traverse' . proextract
  {-# INLINE traverse' #-}
  wander f = returnCoyoneda . wander f . proextract
  {-# INLINE wander #-}
