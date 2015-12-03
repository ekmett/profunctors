{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
#if __GLASGOW_HASKELL__ >= 702 && __GLASGOW_HASKELL__ <= 708
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
module Data.Profunctor.Tambara.Choice
  ( TambaraChoice(..)
  , tambaraChoice, untambaraChoice
  , PastroChoice(..)
  , CotambaraChoice(..)
  , cotambaraChoice, uncotambaraChoice
  , CopastroChoice(..)
  ) where

import Control.Arrow
import Control.Category
import Data.Profunctor
import Data.Profunctor.Adjunction
import Data.Profunctor.Monad
import Data.Profunctor.Unsafe
import Prelude hiding (id,(.))

----------------------------------------------------------------------------
-- * TambaraChoice
----------------------------------------------------------------------------

-- | TambaraChoice is cofreely adjoins strength with respect to Either.
--
-- Note: this is not dual to 'Data.Profunctor.Tambara.Tambara'. It is 'Data.Profunctor.Tambara.Tambara' with respect to a different tensor.
newtype TambaraChoice p a b = TambaraChoice { runTambaraChoice :: forall c. p (Either a c) (Either b c) }

instance ProfunctorFunctor TambaraChoice where
  promap f (TambaraChoice p) = TambaraChoice (f p)

instance ProfunctorComonad TambaraChoice where
  proextract (TambaraChoice p)   = dimap Left (\(Left a) -> a) p
  produplicate (TambaraChoice p) = TambaraChoice (TambaraChoice $ dimap hither yon p) where
    hither :: Either (Either a b) c -> Either a (Either b c)
    hither (Left (Left x))   = Left x
    hither (Left (Right y))  = Right (Left y)
    hither (Right z)         = Right (Right z)

    yon    :: Either a (Either b c) -> Either (Either a b) c
    yon    (Left x)          = Left (Left x)
    yon    (Right (Left y))  = Left (Right y)
    yon    (Right (Right z)) = Right z

instance Profunctor p => Profunctor (TambaraChoice p) where
  dimap f g (TambaraChoice p) = TambaraChoice $ dimap (left f) (left g) p
  {-# INLINE dimap #-}

instance Profunctor p => Choice (TambaraChoice p) where
  left' = runTambaraChoice . produplicate
  {-# INLINE left' #-}

instance Category p => Category (TambaraChoice p) where
  id = TambaraChoice id
  TambaraChoice p . TambaraChoice q = TambaraChoice (p . q)

instance Profunctor p => Functor (TambaraChoice p a) where
  fmap = rmap

-- |
-- @
-- 'tambaraChoice' '.' 'untambaraChoice' ≡ 'id'
-- 'untambaraChoice' '.' 'tambaraChoice' ≡ 'id'
-- @
tambaraChoice :: Choice p => (p :-> q) -> p :-> TambaraChoice q
tambaraChoice f p = TambaraChoice $ f $ left' p

-- |
-- @
-- 'tambaraChoice' '.' 'untambaraChoice' ≡ 'id'
-- 'untambaraChoice' '.' 'tambaraChoice' ≡ 'id'
-- @
untambaraChoice :: Profunctor q => (p :-> TambaraChoice q) -> p :-> q
untambaraChoice f p = dimap Left (\(Left a) -> a) $ runTambaraChoice $ f p

----------------------------------------------------------------------------
-- * PastroChoice
----------------------------------------------------------------------------

-- | PastroChoice -| TambaraChoice
--
-- PastroChoice freely constructs strength with respect to Either.
data PastroChoice p a b where
  PastroChoice :: (Either y z -> b) -> p x y -> (a -> Either x z) -> PastroChoice p a b

instance Profunctor p => Profunctor (PastroChoice p) where
  dimap f g (PastroChoice l m r) = PastroChoice (g . l) m (r . f)
  lmap f (PastroChoice l m r) = PastroChoice l m (r . f)
  rmap g (PastroChoice l m r) = PastroChoice (g . l) m r
  w #. PastroChoice l m r = PastroChoice (w #. l) m r
  PastroChoice l m r .# w = PastroChoice l m (r .# w)

instance ProfunctorAdjunction PastroChoice TambaraChoice where
  counit (PastroChoice f (TambaraChoice g) h) = dimap h f g
  unit p = TambaraChoice $ PastroChoice id p id

instance ProfunctorFunctor PastroChoice where
  promap f (PastroChoice l m r) = PastroChoice l (f m) r

instance ProfunctorMonad PastroChoice where
  proreturn p = PastroChoice (\(Left a)-> a) p Left
  projoin (PastroChoice l (PastroChoice m n o) q) = PastroChoice lm n oq where
    oq a = case q a of
      Left b -> Left <$> o b
      Right z -> Right (Right z)
    lm (Left x) = l $ Left $ m $ Left x
    lm (Right (Left y)) = l $ Left $ m $ Right y
    lm (Right (Right z)) = l $ Right z

instance Profunctor p => Choice (PastroChoice p) where
  left' (PastroChoice l m r) = PastroChoice l' m r' where
    r' = either (fmap Left . r) (Right . Right)
    l' (Left y)          = Left (l (Left y))
    l' (Right (Left z))  = Left (l (Right z))
    l' (Right (Right c)) = Right c
  right' (PastroChoice l m r) = PastroChoice l' m r' where
    r' = either (Right . Left) (fmap Right . r)
    l' (Right (Left c))  = Left c
    l' (Right (Right z)) = Right (l (Right z))
    l' (Left y)          = Right (l (Left y))

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
