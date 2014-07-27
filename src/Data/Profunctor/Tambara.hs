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
  , Cotambara(..)
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
  first' (Tambara p) = Tambara $ dimap hither yon p where
    hither ~(~(x,y),z) = (x,(y,z))
    yon    ~(x,~(y,z)) = ((x,y),z)
  {-# INLINE first' #-}

instance Choice p => Choice (Tambara p) where
  left' (Tambara f) = Tambara $ dimap hither yon $ left' f where
    hither (Left y, s) = Left (y, s)
    hither (Right z, s) = Right (z, s)
    yon (Left (y, s)) = (Left y, s)
    yon (Right (z, s)) = (Right z, s)
  
instance Category p => Category (Tambara p) where
  id = Tambara id
  Tambara p . Tambara q = Tambara (p . q)

instance Arrow p => Arrow (Tambara p) where
  arr f = Tambara (arr (\(x, s) -> (f x, s)))
  first (Tambara f) = Tambara (arr go . first f . arr go) where
    go ~(~(x,y),z) = ((x,z),y)

instance ArrowChoice p => ArrowChoice (Tambara p) where
  left (Tambara f) = Tambara (arr yon . left f . arr hither) where
    hither (Left y, s) = Left (y, s)
    hither (Right z, s) = Right (z, s)
    yon (Left (y, s)) = (Left y, s)
    yon (Right (z, s)) = (Right z, s)

instance ArrowApply p => ArrowApply (Tambara p) where
  app = Tambara $ app . arr (\((Tambara f, x), s) -> (f, (x, s)))

instance ArrowLoop p => ArrowLoop (Tambara p) where
  loop (Tambara f) = Tambara (loop (arr go . f . arr go)) where
    go ~(~(x,y),z) = ((x,z),y)

instance ArrowZero p => ArrowZero (Tambara p) where
  zeroArrow = Tambara zeroArrow

instance ArrowPlus p => ArrowPlus (Tambara p) where
  Tambara f <+> Tambara g = Tambara (f <+> g)

-- TODO: (Strong p, Profunctor q) => Iso' (p ~> q) (p ~> Tambara q)

newtype Cotambara p a b = Cotambara { runCotambara :: forall c. p (Either a c) (Either b c) }

instance Profunctor p => Profunctor (Cotambara p) where
  dimap f g (Cotambara p) = Cotambara $ dimap (left f) (left g) p
  {-# INLINE dimap #-}

instance Profunctor p => Choice (Cotambara p) where
  left' (Cotambara p) = Cotambara (dimap hither yon p) where
    hither (Left (Left x))   = Left x
    hither (Left (Right y))  = Right (Left y)
    hither (Right z)         = Right (Right z)
    yon    (Left x)          = Left (Left x)
    yon    (Right (Left y))  = Left (Right y)
    yon    (Right (Right z)) = Right z
  {-# INLINE left' #-}

-- TODO: (Profunctor p, Choice q) => Iso' (p ~> q) (Cotambara p ~> q)
