{-# LANGUAGE GADTs #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Profunctor.Trace
-- Copyright   :  (C) 2011-2012 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  GADTs
--
----------------------------------------------------------------------------
module Data.Profunctor.Trace
  ( Trace(..)
  ) where

-- | Coend of 'Data.Profunctor.Profunctor' from @Hask -> Hask@.
data Trace f where
  Trace :: f a a -> Trace f
