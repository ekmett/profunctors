-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2011-2015 Edward Kmett,
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
-- For a good explanation of profunctors in Haskell see Dan Piponi's article:
--
-- <http://blog.sigfpe.com/2011/07/profunctors-in-haskell.html>
--
-- For more information on strength and costrength, see:
--
-- <http://comonad.com/reader/2008/deriving-strength-from-laziness/>
----------------------------------------------------------------------------
module Data.Profunctor
  (
  -- * Profunctors
    Profunctor(dimap,lmap,rmap)
  -- ** Profunctorial Strength
  , Strong(..)
  , uncurry'
  , Choice(..)
  -- ** Closed
  , Closed(..)
  , curry'
  , Mapping(..)
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
import Data.Profunctor.Closed
import Data.Profunctor.Mapping
import Data.Profunctor.Strong
import Data.Profunctor.Types
