module Data.Profunctor.Cayley where

import Control.Applicative
import Control.Category
import Data.Profunctor.Unsafe
import Data.Profunctor
import Prelude hiding ((.), id)

-- static arrows
newtype Cayley f p a b = Cayley { runCayley :: f (p a b) }

instance (Functor f, Profunctor p) => Profunctor (Cayley f p) where
  dimap f g (Cayley fpab) = Cayley $ dimap f g <$> fpab

instance (Functor f, Strong p) => Strong (Cayley f p) where
  first' (Cayley fpab) = Cayley $ first' <$> fpab
  second' (Cayley fpab) = Cayley $ second' <$> fpab

instance (Functor f, Choice p) => Choice (Cayley f p) where
  left'  (Cayley fpab) = Cayley $ left' <$> fpab
  right' (Cayley fpab) = Cayley $ right' <$> fpab

instance (Applicative f, Category p) => Category (Cayley f p) where
  id = Cayley $ pure id
  Cayley fpbc . Cayley fpab = Cayley $ liftA2 (.) fpbc fpab

-- TODO: arrow typeclasses
