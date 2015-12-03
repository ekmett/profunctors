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
module Data.Profunctor.Cochoice
  ( Cochoice(..)
  , CotambaraChoice(..)
  , cotambaraChoice, uncotambaraChoice
  , CopastroChoice(..)
  ) where

import Control.Applicative hiding (WrappedArrow(..))
import Control.Category
import Control.Comonad
import Data.Bifunctor.Product (Product(..))
import Data.Bifunctor.Tannen (Tannen(..))
import Data.Profunctor.Adjunction
import Data.Profunctor.Monad
import Data.Profunctor.Types
import Prelude hiding (id,(.))

--------------------------------------------------------------------------------
-- * Costrength for Either
--------------------------------------------------------------------------------

class Profunctor p => Cochoice p where
  unleft  :: p (Either a d) (Either b d) -> p a b
  unleft = unright . dimap (either Right Left) (either Right Left)

  unright :: p (Either d a) (Either d b) -> p a b
  unright = unleft . dimap (either Right Left) (either Right Left)

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 708
  {-# MINIMAL unleft | unright #-}
#endif

instance Cochoice (->) where
  unleft f = go . Left where go = either id (go . Right) . f
  unright f = go . Right where go = either (go . Left) id . f

instance Applicative f => Cochoice (Costar f) where
  unleft (Costar f) = Costar (go . fmap Left)
    where go = either id (go . pure . Right) . f

-- NB: Another instance that's highly questionable
instance Traversable f => Cochoice (Star f) where
  unright (Star f) = Star (go . Right)
    where go = either (go . Left) id . sequence . f

instance (Functor f, Cochoice p) => Cochoice (Tannen f p) where
  unleft (Tannen fp) = Tannen (fmap unleft fp)
  {-# INLINE unleft #-}
  unright (Tannen fp) = Tannen (fmap unright fp)
  {-# INLINE unright #-}

instance (Cochoice p, Cochoice q) => Cochoice (Product p q) where
  unleft (Pair p q) = Pair (unleft p) (unleft q)
  unright (Pair p q) = Pair (unright p) (unright q)

----------------------------------------------------------------------------
-- * CotambaraChoice
----------------------------------------------------------------------------

-- | 'CotambaraChoice' cofreely constructs costrength with respect to 'Either' (aka 'Choice')
data CotambaraChoice q a b where
    CotambaraChoice :: Cochoice r => (r :-> q) -> r a b -> CotambaraChoice q a b

instance Profunctor p => Profunctor (CotambaraChoice p) where
  lmap f (CotambaraChoice n p) = CotambaraChoice n (lmap f p)
  rmap g (CotambaraChoice n p) = CotambaraChoice n (rmap g p)
  dimap f g (CotambaraChoice n p) = CotambaraChoice n (dimap f g p)

instance ProfunctorFunctor CotambaraChoice where
  promap f (CotambaraChoice n p) = CotambaraChoice (f . n) p

instance ProfunctorComonad CotambaraChoice where
  proextract (CotambaraChoice n p)  = n p
  produplicate (CotambaraChoice n p) = CotambaraChoice id (CotambaraChoice n p)

instance Profunctor p => Cochoice (CotambaraChoice p) where
  unleft (CotambaraChoice n p) = CotambaraChoice n (unleft p)
  unright (CotambaraChoice n p) = CotambaraChoice n (unright p)

instance Profunctor p => Functor (CotambaraChoice p a) where
  fmap = rmap

-- |
-- @
-- 'cotambaraChoice' '.' 'uncotambaraChoice' ≡ 'id'
-- 'uncotambaraChoice' '.' 'cotambaraChoice' ≡ 'id'
-- @
cotambaraChoice :: Cochoice p => (p :-> q) -> p :-> CotambaraChoice q
cotambaraChoice = CotambaraChoice

-- |
-- @
-- 'cotambaraChoice' '.' 'uncotambaraChoice' ≡ 'id'
-- 'uncotambaraChoice' '.' 'cotambaraChoice' ≡ 'id'
-- @
uncotambaraChoice :: Profunctor q => (p :-> CotambaraChoice q) -> p :-> q
uncotambaraChoice f p = proextract (f p)

----------------------------------------------------------------------------
-- * Copastro
----------------------------------------------------------------------------

-- | CopastroChoice -| CotambaraChoice
--
-- 'CopastroChoice' freely constructs costrength with respect to 'Either' (aka 'Choice')
newtype CopastroChoice p a b = CopastroChoice { runCopastroChoice :: forall r. Cochoice r => (p :-> r) -> r a b }

instance Profunctor p => Profunctor (CopastroChoice p) where
  dimap f g (CopastroChoice h) = CopastroChoice $ \ n -> dimap f g (h n)
  lmap f (CopastroChoice h) = CopastroChoice $ \ n -> lmap f (h n)
  rmap g (CopastroChoice h) = CopastroChoice $ \ n -> rmap g (h n)

instance ProfunctorAdjunction CopastroChoice CotambaraChoice where
 unit p = CotambaraChoice id (proreturn p)
 counit (CopastroChoice h) = proextract (h id)

instance ProfunctorFunctor CopastroChoice where
  promap f (CopastroChoice h) = CopastroChoice $ \n -> h (n . f)

instance ProfunctorMonad CopastroChoice where
  proreturn p = CopastroChoice $ \n -> n p
  projoin p = CopastroChoice $ \c -> runCopastroChoice p (\x -> runCopastroChoice x c)

instance Profunctor p => Cochoice (CopastroChoice p) where
  unleft (CopastroChoice p) = CopastroChoice $ \n -> unleft (p n)
  unright (CopastroChoice p) = CopastroChoice $ \n -> unright (p n)
