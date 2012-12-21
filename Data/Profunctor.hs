module Data.Profunctor
  ( Profunctor(..)
  , UpStar(..)
  , DownStar(..)
  , WrappedArrow(..)
  ) where

import Control.Arrow
import Control.Category
import Control.Comonad (Cokleisli(..))
import Control.Monad (liftM)
import Data.Tagged
import Prelude hiding (id,(.))

class Profunctor h where
  lmap :: (a -> b) -> h b c -> h a c
  rmap :: (b -> c) -> h a b -> h a c

instance Profunctor (->) where
  lmap = flip (.)
  rmap = (.)

instance Profunctor Tagged where
  lmap _ = retag
  rmap = fmap

newtype UpStar f d c = UpStar { runUpStar :: d -> f c } 
instance Functor f => Profunctor (UpStar f) where
  lmap k (UpStar f) = UpStar (f . k)
  rmap k (UpStar f) = UpStar (fmap k . f)

instance Functor f => Functor (UpStar f a) where
  fmap = rmap 

newtype DownStar f d c = DownStar { runDownStar :: f d -> c } 
instance Functor f => Profunctor (DownStar f) where
  lmap k (DownStar f) = DownStar (f . fmap k)
  rmap k (DownStar f) = DownStar (k . f)

instance Functor (DownStar f a) where
  fmap k (DownStar f) = DownStar (k . f)

newtype WrappedArrow k a b = WrapArrow { unwrapArrow :: k a b } 

instance Category k => Category (WrappedArrow k) where
  WrapArrow f . WrapArrow g = WrapArrow (f . g)
  id = WrapArrow id

instance Arrow k => Arrow (WrappedArrow k) where
  arr = WrapArrow . arr
  first = WrapArrow . first . unwrapArrow
  second = WrapArrow . second . unwrapArrow 
  WrapArrow a *** WrapArrow b = WrapArrow (a *** b)
  WrapArrow a &&& WrapArrow b = WrapArrow (a &&& b)
  
instance ArrowZero k => ArrowZero (WrappedArrow k) where
  zeroArrow = WrapArrow zeroArrow

instance ArrowChoice k => ArrowChoice (WrappedArrow k) where
  left = WrapArrow . left . unwrapArrow
  right = WrapArrow . right . unwrapArrow
  WrapArrow a +++ WrapArrow b = WrapArrow (a +++ b)
  WrapArrow a ||| WrapArrow b = WrapArrow (a ||| b)
  
instance ArrowApply k => ArrowApply (WrappedArrow k) where
  app = WrapArrow $ app . arr (first unwrapArrow)

instance ArrowLoop k => ArrowLoop (WrappedArrow k) where
  loop = WrapArrow . loop . unwrapArrow 

instance Arrow k => Profunctor (WrappedArrow k) where
  lmap = (^>>)
  rmap = (^<<)

instance Monad m => Profunctor (Kleisli m) where
  lmap k (Kleisli f) = Kleisli (f . k)
  rmap k (Kleisli f) = Kleisli (liftM k . f)

instance Functor w => Profunctor (Cokleisli w) where
  lmap k (Cokleisli f) = Cokleisli (f . fmap k)
  rmap k (Cokleisli f) = Cokleisli (k . f)
