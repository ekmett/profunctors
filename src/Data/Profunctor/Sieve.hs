{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE Trustworthy #-}
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2015 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  MPTCs, fundeps
--
----------------------------------------------------------------------------
module Data.Profunctor.Sieve
  ( Sieve(..)
  , Cosieve(..)
  ) where

import Control.Applicative
import Control.Arrow
import Control.Comonad
import Data.Functor.Identity
import Data.Profunctor
import Data.Proxy
import Data.Tagged

-- | A 'Profunctor' @p@ is a 'Sieve' __on__ @f@ if it is a subprofunctor of @'Star' f@.
--
-- That is to say it is a subset of @Hom(-,f=)@ closed under 'lmap' and 'rmap'.
--
-- Alternately, you can view it as a sieve __in__ the comma category @Hask/f@.
class (Profunctor p, Functor f) => Sieve p f | p -> f where
  sieve :: p a b -> a -> f b

instance Sieve (->) Identity where
  sieve f = Identity . f
  {-# INLINE sieve #-}

instance (Monad m, Functor m) => Sieve (Kleisli m) m where
  sieve = runKleisli
  {-# INLINE sieve #-}

instance Functor f => Sieve (Star f) f where
  sieve = runStar
  {-# INLINE sieve #-}

instance Sieve (Forget r) (Const r) where
  sieve = (Const .) . runForget
  {-# INLINE sieve #-}

-- | A 'Profunctor' @p@ is a 'Cosieve' __on__ @f@ if it is a subprofunctor of @'Costar' f@.
--
-- That is to say it is a subset of @Hom(f-,=)@ closed under 'lmap' and 'rmap'.
--
-- Alternately, you can view it as a cosieve __in__ the comma category @f/Hask@.
class (Profunctor p, Functor f) => Cosieve p f | p -> f where
  cosieve :: p a b -> f a -> b

instance Cosieve (->) Identity where
  cosieve f (Identity d) = f d
  {-# INLINE cosieve #-}

instance Functor w => Cosieve (Cokleisli w) w where
  cosieve = runCokleisli
  {-# INLINE cosieve #-}

instance Cosieve Tagged Proxy where
  cosieve (Tagged a) _ = a
  {-# INLINE cosieve #-}

instance Functor f => Cosieve (Costar f) f where
  cosieve = runCostar
  {-# INLINE cosieve #-}
