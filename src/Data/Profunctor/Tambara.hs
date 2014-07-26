{-# LANGUAGE CPP #-}
{-# LANGUAGE Rank2Types #-}
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2014 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  Rank2Types
--
----------------------------------------------------------------------------
module Data.Profunctor.Tambara
  ( Tambara(..)
  ) where

import Control.Arrow
import Control.Category
import Data.Profunctor
import Prelude hiding (id,(.))

newtype Tambara p a b = Tambara { runTambara :: forall c. p (a, c) (b, c) }

instance Profunctor p => Profunctor (Tambara p) where
  dimap f g (Tambara p) = Tambara $ dimap (first f) (first g) p
  {-# INLINE dimap #-}

instance Profunctor p => Strong (Tambara p) where
  first' (Tambara p) = Tambara (dimap hither yon p) where
    hither ((x,y),z) = (x,(y,z))
    yon    (x,(y,z)) = ((x,y),z)
  {-# INLINE first' #-}

instance Category p => Category (Tambara p) where
  id = Tambara id
  Tambara p . Tambara q = Tambara (p . q)

-- TODO: (Strong p, Profunctor q) => Iso' (p ~> q) (p ~> Tambara q)
