-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2014 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  portable
--
----------------------------------------------------------------------------
module Data.Profunctor.Cayley where

import Control.Applicative
import Control.Arrow
import Control.Category
import Data.Profunctor.Unsafe
import Data.Profunctor
import Prelude hiding ((.), id)

-- static arrows
newtype Cayley f p a b = Cayley { runCayley :: f (p a b) }

instance (Functor f, Profunctor p) => Profunctor (Cayley f p) where
  dimap f g = Cayley . fmap (dimap f g) . runCayley

instance (Functor f, Strong p) => Strong (Cayley f p) where
  first'  = Cayley . fmap first' . runCayley
  second' = Cayley . fmap second' . runCayley

instance (Functor f, Choice p) => Choice (Cayley f p) where
  left'   = Cayley . fmap left' . runCayley
  right'  = Cayley . fmap right' . runCayley

instance (Applicative f, Category p) => Category (Cayley f p) where
  id = Cayley $ pure id
  Cayley fpbc . Cayley fpab = Cayley $ liftA2 (.) fpbc fpab

instance (Applicative f, Arrow p) => Arrow (Cayley f p) where
  arr f = Cayley $ pure $ arr f
  first = Cayley . fmap first . runCayley
  second = Cayley . fmap second . runCayley
  Cayley ab *** Cayley cd = Cayley $ liftA2 (***) ab cd
  Cayley ab &&& Cayley ac = Cayley $ liftA2 (&&&) ab ac

instance (Applicative f, ArrowChoice p) => ArrowChoice (Cayley f p) where
  left  = Cayley . fmap left . runCayley
  right = Cayley . fmap right . runCayley
  Cayley ab +++ Cayley cd = Cayley $ liftA2 (+++) ab cd
  Cayley ac ||| Cayley bc = Cayley $ liftA2 (|||) ac bc
  
instance (Applicative f, ArrowLoop p) => ArrowLoop (Cayley f p) where
  loop = Cayley . fmap loop . runCayley

instance (Applicative f, ArrowZero p) => ArrowZero (Cayley f p) where
  zeroArrow = Cayley $ pure zeroArrow

instance (Applicative f, ArrowPlus p) => ArrowPlus (Cayley f p) where
  Cayley f <+> Cayley g = Cayley (liftA2 (<+>) f g)
