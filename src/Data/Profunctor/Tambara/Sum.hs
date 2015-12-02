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
module Data.Profunctor.Tambara.Sum
  ( TambaraSum(..)
  , tambaraSum, untambaraSum
  , PastroSum(..)
  ) where

import Control.Applicative
import Control.Arrow
import Control.Category
import Data.Monoid
import Data.Profunctor
import Data.Profunctor.Adjunction
import Data.Profunctor.Monad
import Data.Profunctor.Unsafe
import Prelude hiding (id,(.))

----------------------------------------------------------------------------
-- * TambaraSum
----------------------------------------------------------------------------

-- | TambaraSum is freely adjoins respect for cocartesian structure to a profunctor
--
-- Note: this is not dual to 'Tambara'. It is 'Tambara' with respect to a different tensor.
newtype TambaraSum p a b = TambaraSum { runTambaraSum :: forall c. p (Either a c) (Either b c) }

instance ProfunctorFunctor TambaraSum where
  promap f (TambaraSum p) = TambaraSum (f p)

instance ProfunctorComonad TambaraSum where
  proextract (TambaraSum p)   = dimap Left (\(Left a) -> a) p
  produplicate (TambaraSum p) = TambaraSum (TambaraSum $ dimap hither yon p) where
    hither :: Either (Either a b) c -> Either a (Either b c)
    hither (Left (Left x))   = Left x
    hither (Left (Right y))  = Right (Left y)
    hither (Right z)         = Right (Right z)

    yon    :: Either a (Either b c) -> Either (Either a b) c
    yon    (Left x)          = Left (Left x)
    yon    (Right (Left y))  = Left (Right y)
    yon    (Right (Right z)) = Right z

instance Profunctor p => Profunctor (TambaraSum p) where
  dimap f g (TambaraSum p) = TambaraSum $ dimap (left f) (left g) p
  {-# INLINE dimap #-}

instance Profunctor p => Choice (TambaraSum p) where
  left' = runTambaraSum . produplicate
  {-# INLINE left' #-}

instance Category p => Category (TambaraSum p) where
  id = TambaraSum id
  TambaraSum p . TambaraSum q = TambaraSum (p . q)

instance Profunctor p => Functor (TambaraSum p a) where
  fmap = rmap

-- |
-- @
-- 'tambaraSum' '.' 'untambaraSum' ≡ 'id'
-- 'untambaraSum' '.' 'tambaraSum' ≡ 'id'
-- @
tambaraSum :: Choice p => (p :-> q) -> p :-> TambaraSum q
tambaraSum f p = TambaraSum $ f $ left' p

-- |
-- @
-- 'tambaraSum' '.' 'untambaraSum' ≡ 'id'
-- 'untambaraSum' '.' 'tambaraSum' ≡ 'id'
-- @
untambaraSum :: Profunctor q => (p :-> TambaraSum q) -> p :-> q
untambaraSum f p = dimap Left (\(Left a) -> a) $ runTambaraSum $ f p

----------------------------------------------------------------------------
-- * PastroSum
----------------------------------------------------------------------------

-- | PastroSum -| TambaraSum
data PastroSum p a b where
  PastroSum :: (Either y z -> b) -> p x y -> (a -> Either x z) -> PastroSum p a b

instance Profunctor p => Profunctor (PastroSum p) where
  dimap f g (PastroSum l m r) = PastroSum (g . l) m (r . f)
  lmap f (PastroSum l m r) = PastroSum l m (r . f)
  rmap g (PastroSum l m r) = PastroSum (g . l) m r
  w #. PastroSum l m r = PastroSum (w #. l) m r
  PastroSum l m r .# w = PastroSum l m (r .# w)

instance ProfunctorAdjunction PastroSum TambaraSum where
  counit (PastroSum f (TambaraSum g) h) = dimap h f g
  unit p = TambaraSum $ PastroSum id p id

instance ProfunctorFunctor PastroSum where
  promap f (PastroSum l m r) = PastroSum l (f m) r

instance ProfunctorMonad PastroSum where
  proreturn p = PastroSum (\(Left a)-> a) p Left
  projoin (PastroSum l (PastroSum m n o) q) = PastroSum lm n oq where
    oq a = case q a of
      Left b -> case o b of
        Left c -> Left c
        Right z -> Right (Left z)
      Right z -> Right (Right z)
    lm (Left x) = l $ Left $ m $ Left x
    lm (Right (Left y)) = l $ Left $ m $ Right y
    lm (Right (Right z)) = l $ Right z
