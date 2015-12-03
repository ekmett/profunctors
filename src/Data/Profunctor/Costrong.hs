{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
#if __GLASGOW_HASKELL__ >= 704 && __GLASGOW_HASKELL__ < 708
{-# LANGUAGE Trustworthy #-}
#endif
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2014-2015 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  Rank2Types
--
----------------------------------------------------------------------------
module Data.Profunctor.Costrong
  ( Costrong(..)
  , Cotambara(..)
  , cotambara, uncotambara
  , Copastro(..)
  ) where

import Control.Applicative hiding (WrappedArrow(..))
import Control.Arrow
import Control.Category
import Control.Comonad
import Control.Monad (liftM)
import Control.Monad.Fix
import Data.Bifunctor.Product (Product(..))
import Data.Bifunctor.Tannen (Tannen(..))
import Data.Profunctor.Adjunction
import Data.Profunctor.Monad
import Data.Profunctor.Types
import Data.Tagged
import Data.Tuple
import Prelude hiding (id,(.))

--------------------------------------------------------------------------------
-- * Costrength for (,)
--------------------------------------------------------------------------------

-- | Analogous to 'ArrowLoop', 'loop' = 'unfirst'
class Profunctor p => Costrong p where
  unfirst  :: p (a, d) (b, d) -> p a b
  unfirst = unsecond . dimap swap swap

  unsecond :: p (d, a) (d, b) -> p a b
  unsecond = unfirst . dimap swap swap

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 708
  {-# MINIMAL unfirst | unsecond #-}
#endif

instance Costrong (->) where
  unfirst f a = b where (b, d) = f (a, d)
  unsecond f a = b where (d, b) = f (d, a)

instance Functor f => Costrong (Costar f) where
  unfirst (Costar f) = Costar f'
    where f' fa = b where (b, d) = f ((\a -> (a, d)) <$> fa)
  unsecond (Costar f) = Costar f'
    where f' fa = b where (d, b) = f ((,) d <$> fa)

instance Costrong Tagged where
  unfirst (Tagged bd) = Tagged (fst bd)
  unsecond (Tagged db) = Tagged (snd db)

instance ArrowLoop p => Costrong (WrappedArrow p) where
  unfirst (WrapArrow k) = WrapArrow (loop k)

instance MonadFix m => Costrong (Kleisli m) where
  unfirst (Kleisli f) = Kleisli (liftM fst . mfix . f')
    where f' x y = f (x, snd y)

instance Functor f => Costrong (Cokleisli f) where
  unfirst (Cokleisli f) = Cokleisli f'
    where f' fa = b where (b, d) = f ((\a -> (a, d)) <$> fa)

instance (Functor f, Costrong p) => Costrong (Tannen f p) where
  unfirst (Tannen fp) = Tannen (fmap unfirst fp)
  unsecond (Tannen fp) = Tannen (fmap unsecond fp)

instance (Costrong p, Costrong q) => Costrong (Product p q) where
  unfirst (Pair p q) = Pair (unfirst p) (unfirst q)
  unsecond (Pair p q) = Pair (unsecond p) (unsecond q)

----------------------------------------------------------------------------
-- * Cotambara
----------------------------------------------------------------------------

-- | Cotambara cofreely constructs costrength
data Cotambara q a b where
    Cotambara :: Costrong r => (r :-> q) -> r a b -> Cotambara q a b

instance Profunctor p => Profunctor (Cotambara p) where
  lmap f (Cotambara n p) = Cotambara n (lmap f p)
  rmap g (Cotambara n p) = Cotambara n (rmap g p)
  dimap f g (Cotambara n p) = Cotambara n (dimap f g p)

instance ProfunctorFunctor Cotambara where
  promap f (Cotambara n p) = Cotambara (f . n) p

instance ProfunctorComonad Cotambara where
  proextract (Cotambara n p)  = n p
  produplicate (Cotambara n p) = Cotambara id (Cotambara n p)

instance Profunctor p => Costrong (Cotambara p) where
  unfirst (Cotambara n p) = Cotambara n (unfirst p)

instance Profunctor p => Functor (Cotambara p a) where
  fmap = rmap

-- |
-- @
-- 'cotambara' '.' 'uncotambara' ≡ 'id'
-- 'uncotambara' '.' 'cotambara' ≡ 'id'
-- @
cotambara :: Costrong p => (p :-> q) -> p :-> Cotambara q
cotambara = Cotambara

-- |
-- @
-- 'cotambara' '.' 'uncotambara' ≡ 'id'
-- 'uncotambara' '.' 'cotambara' ≡ 'id'
-- @
uncotambara :: Profunctor q => (p :-> Cotambara q) -> p :-> q
uncotambara f p = proextract (f p)

----------------------------------------------------------------------------
-- * Copastro
----------------------------------------------------------------------------

-- | Copastro -| Cotambara
--
-- Copastro freely constructs costrength
newtype Copastro p a b = Copastro { runCopastro :: forall r. Costrong r => (p :-> r) -> r a b }

instance Profunctor p => Profunctor (Copastro p) where
  dimap f g (Copastro h) = Copastro $ \ n -> dimap f g (h n)
  lmap f (Copastro h) = Copastro $ \ n -> lmap f (h n)
  rmap g (Copastro h) = Copastro $ \ n -> rmap g (h n)

instance ProfunctorAdjunction Copastro Cotambara where
 unit p = Cotambara id (proreturn p)
 counit (Copastro h) = proextract (h id)

instance ProfunctorFunctor Copastro where
  promap f (Copastro h) = Copastro $ \n -> h (n . f)

instance ProfunctorMonad Copastro where
  proreturn p = Copastro $ \n -> n p
  projoin p = Copastro $ \c -> runCopastro p (\x -> runCopastro x c)

instance Profunctor p => Costrong (Copastro p) where
  unfirst (Copastro p) = Copastro $ \n -> unfirst (p n)
  unsecond (Copastro p) = Copastro $ \n -> unsecond (p n)
