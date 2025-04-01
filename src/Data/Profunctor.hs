{-# LANGUAGE Safe #-}

-- |
-- Copyright   :  (C) 2011-2021 Edward Kmett,
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
-- For a good explanation of profunctors in Haskell see Dan Piponi's article:
--
-- <https://github.com/dpiponi/StableBlog/blob/main/Profunctors/Profunctors.pdf>
--
-- For more information on strength and costrength, see:
--
-- <http://comonad.com/reader/2008/deriving-strength-from-laziness/>

module Data.Profunctor
(
-- * Profunctors
  Profunctor(dimap,lmap,rmap)
-- ** Profunctorial Strength
, Strong(..)
, uncurry'
, Choice(..)
-- ** Profunctorial Costrength
, Costrong(..)
, Cochoice(..)
-- ** Common Profunctors
, Star(..)
, Costar(..)
, WrappedArrow(..)
, Forget(..)
, (:->)
) where

import Data.Profunctor.Choice
import Data.Profunctor.Strong
import Data.Profunctor.Types
