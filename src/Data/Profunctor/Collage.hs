{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# LANGUAGE CPP #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Profunctor.Collage
-- Copyright   :  (C) 2011-2012 Edward Kmett,
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  MPTCs
--
----------------------------------------------------------------------------
module Data.Profunctor.Collage
  ( Collage(..)
  ) where

import Data.Semigroupoid
import Data.Semigroupoid.Ob
import Data.Semigroupoid.Coproduct (L, R)
import Data.Profunctor

-- | The cograph of a 'Profunctor'.
data Collage k b a where
  L :: (b -> b') -> Collage k (L b) (L b')
  R :: (a -> a') -> Collage k (R a) (R a')
  C :: k b a     -> Collage k (L b) (R a)

instance Profunctor k => Semigroupoid (Collage k) where
  L f `o` L g = L (f . g)
  R f `o` R g = R (f . g)
  R f `o` C g = C (rmap f g)
  C f `o` L g = C (lmap g f)

instance Profunctor k => Ob (Collage k) (L a) where
  semiid = L semiid

instance Profunctor k => Ob (Collage k) (R a) where
  semiid = R semiid
