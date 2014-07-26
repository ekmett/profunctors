module Data.Profunctor.Closed where

import Control.Arrow
import Control.Comonad
import Data.Distributive
import Data.Monoid
import Data.Profunctor
import Data.Tagged

-- | A strong profunctor allows the monoidal structure to pass through.
-- 
-- A closed profunctor allows the closed structure to pass through.
class Profunctor p => Closed p where
  closed :: p a b -> p (x -> a) (x -> b)

instance Closed Tagged where
  closed (Tagged b) = Tagged (const b)

instance Closed (->) where
  closed = (.)

instance Functor f => Closed (DownStar f) where
  closed (DownStar fab) = DownStar $ \fxa x -> fab (fmap ($x) fxa)
 
instance Functor f => Closed (Cokleisli f) where
  closed (Cokleisli fab) = Cokleisli $ \fxa x -> fab (fmap ($x) fxa)

instance Distributive f => Closed (UpStar f) where
  closed (UpStar afb) = UpStar $ \xa -> distribute $ \x -> afb (xa x)

instance (Distributive f, Monad f) => Closed (Kleisli f) where
  closed (Kleisli afb) = Kleisli $ \xa -> distribute $ \x -> afb (xa x)

instance Monoid r => Closed (Forget r) where
  closed _ = Forget $ \_ -> mempty
