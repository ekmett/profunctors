{-# LANGUAGE PolyKinds #-}
{-# Language DeriveDataTypeable #-}
{-# Language DeriveFunctor #-}
{-# Language DeriveGeneric #-}
{-# Language DerivingStrategies #-}
{-# Language StandaloneDeriving #-}
{-# Language Trustworthy #-}
{-# Language UndecidableInstances #-}

-- | Fix points of functors over profunctors

module Data.Profunctor.Fix
( Fix(..)
) where

import Data.Data
import Data.Profunctor.Unsafe
import Data.Profunctor.Functor
import GHC.Generics

-- Fix :: ((k1 -> k2 -> *) -> k1 -> k2 -> *) -> k1 -> k2 -> *
newtype Fix f a b = In
  { out :: f (Fix f) a b
  } deriving (Generic, Generic1)

deriving stock instance Functor (f (Fix f) a) => Functor (Fix f a)
deriving stock instance 
  ( Data (f (Fix f) a b)
  , Typeable i
  , Typeable j
  , Typeable f
  , Typeable a
  , Typeable b
  ) => Data (Fix f (a :: i) (b :: j))

instance ProfunctorFunctor f => Profunctor (Fix f) where
  dimap f g (In p) = In (dimap f g p)
  {-# inline dimap #-}
  rmap f (In p) = In (rmap f p)
  {-# inline rmap #-}
  lmap f (In p) = In (lmap f p)
  {-# inline lmap #-}
  x #. In p = In (x #. p)
  {-# inline (#.) #-}
  In p .# y = In (p .# y)
  {-# inline (.#) #-}
