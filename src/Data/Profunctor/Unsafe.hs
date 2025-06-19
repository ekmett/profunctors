{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuantifiedConstraints #-}

-- |
-- Copyright   :  (C) 2011-2021 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
-- For a good explanation of profunctors in Haskell see Dan Piponi's article:
--
-- <https://github.com/dpiponi/StableBlog/blob/main/Profunctors/Profunctors.pdf>
--
-- This module includes /unsafe/ composition operators that are useful in
-- practice when it comes to generating optimal core in GHC.
--
-- If you import this module you are taking upon yourself the obligation
-- that you will only call the operators with @#@ in their names with functions
-- that are operationally identity such as @newtype@ constructors or the field
-- accessor of a @newtype@.
--
-- If you are ever in doubt, use 'rmap' or 'lmap'.

module Data.Profunctor.Unsafe
  (
  -- * Profunctors
    Profunctor(..)
  ) where

import Data.Profunctor.Internal
