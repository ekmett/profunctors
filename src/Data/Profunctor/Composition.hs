{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Profunctor.Composition
-- Copyright   :  (C) 2011-2012 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  GADTs
--
----------------------------------------------------------------------------
module Data.Profunctor.Composition
  (
  -- * Profunctor Composition
    Procompose(..)
  , procomposed
  -- * Lax identity
  , idl
  , idr
  -- * Generalized Composition
  , upstars, kleislis
  , downstars, cokleislis
  ) where

import Control.Arrow
import Control.Category
import Control.Comonad
import Control.Monad (liftM)
import Data.Functor.Compose
import Data.Profunctor
import Data.Profunctor.Rep
import Data.Profunctor.Unsafe
import Prelude hiding ((.),id)

-- * Profunctor Composition

-- | @'Procompose' p q@ is the 'Profunctor' composition of the
-- 'Profunctor's @p@ and @q@.
--
-- For a good explanation of 'Profunctor' composition in Haskell
-- see Dan Piponi's article:
--
-- <http://blog.sigfpe.com/2011/07/profunctors-in-haskell.html>
data Procompose p q d c where
  Procompose :: p d a -> q a c -> Procompose p q d c

procomposed :: Category p => Procompose p p a b -> p a b
procomposed (Procompose pda pac) = pac . pda
{-# INLINE procomposed #-}


instance (Profunctor p, Profunctor q) => Profunctor (Procompose p q) where
  dimap l r (Procompose f g) = Procompose (lmap l f) (rmap r g)
  {-# INLINE dimap #-}
  lmap k (Procompose f g) = Procompose (lmap k f) g
  {-# INLINE rmap #-}
  rmap k (Procompose f g) = Procompose f (rmap k g)
  {-# INLINE lmap #-}
  k #. Procompose f g     = Procompose f (k #. g)
  {-# INLINE ( #. ) #-}
  Procompose f g .# k     = Procompose (f .# k) g
  {-# INLINE ( .# ) #-}

instance Profunctor q => Functor (Procompose p q a) where
  fmap k (Procompose f g) = Procompose f (rmap k g)
  {-# INLINE fmap #-}

-- | The composition of two 'Representable' 'Profunctor's is 'Representable' by
-- the composition of their representations.
instance (Representable p, Representable q) => Representable (Procompose p q) where
  type Rep (Procompose p q) = Compose (Rep p) (Rep q)
  tabulate f = Procompose (tabulate (getCompose . f)) (tabulate id)
  {-# INLINE tabulate #-}
  rep (Procompose f g) d = Compose $ rep g <$> rep f d
  {-# INLINE rep #-}

instance (Corepresentable p, Corepresentable q) => Corepresentable (Procompose p q) where
  type Corep (Procompose p q) = Compose (Corep q) (Corep p)
  cotabulate f = Procompose (cotabulate id) (cotabulate (f . Compose))
  {-# INLINE cotabulate #-}
  corep (Procompose f g) (Compose d) = corep g $ corep f <$> d
  {-# INLINE corep #-}

instance (Strong p, Strong q) => Strong (Procompose p q) where
  first' (Procompose x y) = Procompose (first' x) (first' y)
  {-# INLINE first' #-}
  second' (Procompose x y) = Procompose (second' x) (second' y)
  {-# INLINE second' #-}

instance (Choice p, Choice q) => Choice (Procompose p q) where
  left' (Procompose x y) = Procompose (left' x) (left' y)
  {-# INLINE left' #-}
  right' (Procompose x y) = Procompose (right' x) (right' y)
  {-# INLINE right' #-}


-- * Lax identity

-- | @(->)@ functions as a lax identity for 'Profunctor' composition.
--
-- This provides an 'Iso' for the @lens@ package that witnesses the
-- isomorphism between @'Procompose' (->) q d c@ and @q d c@, which
-- is the left identity law.
--
-- @
-- 'idl' :: 'Profunctor' q => Iso' ('Procompose' (->) q d c) (q d c)
-- @
idl :: (Profunctor p, Profunctor q, Functor f)
    => p (q d c) (f (r d' c')) -> p (Procompose (->) q d c) (f (Procompose (->) r d' c'))
idl = dimap (\(Procompose f g) -> lmap f g) (fmap (Procompose id))

-- | @(->)@ functions as a lax identity for 'Profunctor' composition.
--
-- This provides an 'Iso' for the @lens@ package that witnesses the
-- isomorphism between @'Procompose' q (->) d c@ and @q d c@, which
-- is the right identity law.
--
-- @
-- 'idr' :: 'Profunctor' q => Iso' ('Procompose' q (->) d c) (q d c)
-- @
idr :: (Profunctor p, Profunctor q, Functor f)
    => p (q d c) (f (r d' c')) -> p (Procompose q (->) d c) (f (Procompose r (->) d' c'))
idr = dimap (\(Procompose f g) -> rmap g f) (fmap (`Procompose` id))

-- | 'Profunctor' composition generalizes 'Functor' composition in two ways.
--
-- This is the first, which shows that @exists b. (a -> f b, b -> g c)@ is
-- isomorphic to @a -> f (g c)@.
--
-- @'upstars' :: 'Functor' f => Iso' ('Procompose' ('UpStar' f) ('UpStar' g) d c) ('UpStar' ('Compose' f g) d c)@
upstars :: (Profunctor p, Functor f, Functor h)
        => p (UpStar (Compose f g) d c) (h (UpStar (Compose f' g') d' c'))
        -> p (Procompose (UpStar f) (UpStar g) d c) (h (Procompose (UpStar f') (UpStar g') d' c'))
upstars = dimap hither (fmap yon) where
  hither (Procompose (UpStar dfx) (UpStar xgc)) = UpStar (Compose . fmap xgc . dfx)
  yon (UpStar dfgc) = Procompose (UpStar (getCompose . dfgc)) (UpStar id)

-- | 'Profunctor' composition generalizes 'Functor' composition in two ways.
--
-- This is the second, which shows that @exists b. (f a -> b, g b -> c)@ is
-- isomorphic to @g (f a) -> c@.
--
-- @'downstars' :: 'Functor' f => Iso' ('Procompose' ('DownStar' f) ('DownStar' g) d c) ('DownStar' ('Compose' g f) d c)@
downstars :: (Profunctor p, Functor g, Functor h)
          => p (DownStar (Compose g f) d c) (h (DownStar (Compose g' f') d' c'))
          -> p (Procompose (DownStar f) (DownStar g) d c) (h (Procompose (DownStar f') (DownStar g') d' c'))
downstars = dimap hither (fmap yon) where
  hither (Procompose (DownStar fdx) (DownStar gxc)) = DownStar (gxc . fmap fdx . getCompose)
  yon (DownStar dgfc) = Procompose (DownStar id) (DownStar (dgfc . Compose))

-- | This is a variant on 'upstars' that uses 'Kleisli' instead of 'UpStar'.
--
-- @'kleislis' :: 'Monad' f => Iso' ('Procompose' ('Kleisli' f) ('Kleisli' g) d c) ('Kleisli' ('Compose' f g) d c)@
kleislis :: (Profunctor p, Monad f, Functor h)
        => p (Kleisli (Compose f g) d c) (h (Kleisli (Compose f' g') d' c'))
        -> p (Procompose (Kleisli f) (Kleisli g) d c) (h (Procompose (Kleisli f') (Kleisli g') d' c'))
kleislis = dimap hither (fmap yon) where
  hither (Procompose (Kleisli dfx) (Kleisli xgc)) = Kleisli (Compose . liftM xgc . dfx)
  yon (Kleisli dfgc) = Procompose (Kleisli (getCompose . dfgc)) (Kleisli id)

-- | This is a variant on 'downstars' that uses 'Cokleisli' instead
-- of 'DownStar'.
--
-- @'cokleislis' :: 'Functor' f => Iso' ('Procompose' ('Cokleisli' f) ('Cokleisli' g) d c) ('Cokleisli' ('Compose' g f) d c)@
cokleislis :: (Profunctor p, Functor g, Functor h)
          => p (Cokleisli (Compose g f) d c) (h (Cokleisli (Compose g' f') d' c'))
          -> p (Procompose (Cokleisli f) (Cokleisli g) d c) (h (Procompose (Cokleisli f') (Cokleisli g') d' c'))
cokleislis = dimap hither (fmap yon) where
  hither (Procompose (Cokleisli fdx) (Cokleisli gxc)) = Cokleisli (gxc . fmap fdx . getCompose)
  yon (Cokleisli dgfc) = Procompose (Cokleisli id) (Cokleisli (dgfc . Compose))
