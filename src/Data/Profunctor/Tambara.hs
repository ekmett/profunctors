{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2014 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  Rank2Types
--
----------------------------------------------------------------------------
module Data.Profunctor.Tambara
  ( Tambara(..)
  , tambara, untambara
  , Pastro(..)
  , Cotambara(..)
  , cotambara, uncotambara
  , Copastro(..)
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
-- * Tambara
----------------------------------------------------------------------------

newtype Tambara p a b = Tambara { runTambara :: forall c. p (a, c) (b, c) }

instance Profunctor p => Profunctor (Tambara p) where
  dimap f g (Tambara p) = Tambara $ dimap (first f) (first g) p
  {-# INLINE dimap #-}

instance ProfunctorComonad Tambara where
  proextract (Tambara p) = dimap (\a -> (a,())) fst p
  produplicate (Tambara p) = Tambara (Tambara $ dimap hither yon p) where
    hither ~(~(x,y),z) = (x,(y,z))
    yon    ~(x,~(y,z)) = ((x,y),z)

instance Profunctor p => Strong (Tambara p) where
  first' = runTambara . produplicate
  {-# INLINE first' #-}

instance Choice p => Choice (Tambara p) where
  left' (Tambara f) = Tambara $ dimap hither yon $ left' f where
    hither (Left y, s) = Left (y, s)
    hither (Right z, s) = Right (z, s)
    yon (Left (y, s)) = (Left y, s)
    yon (Right (z, s)) = (Right z, s)

instance Category p => Category (Tambara p) where
  id = Tambara id
  Tambara p . Tambara q = Tambara (p . q)

instance Arrow p => Arrow (Tambara p) where
  arr f = Tambara $ arr $ first f
  first (Tambara f) = Tambara (arr go . first f . arr go) where
    go ~(~(x,y),z) = ((x,z),y)

instance ArrowChoice p => ArrowChoice (Tambara p) where
  left (Tambara f) = Tambara (arr yon . left f . arr hither) where
    hither (Left y, s) = Left (y, s)
    hither (Right z, s) = Right (z, s)
    yon (Left (y, s)) = (Left y, s)
    yon (Right (z, s)) = (Right z, s)

instance ArrowApply p => ArrowApply (Tambara p) where
  app = Tambara $ app . arr (\((Tambara f, x), s) -> (f, (x, s)))

instance ArrowLoop p => ArrowLoop (Tambara p) where
  loop (Tambara f) = Tambara (loop (arr go . f . arr go)) where
    go ~(~(x,y),z) = ((x,z),y)

instance ArrowZero p => ArrowZero (Tambara p) where
  zeroArrow = Tambara zeroArrow

instance ArrowPlus p => ArrowPlus (Tambara p) where
  Tambara f <+> Tambara g = Tambara (f <+> g)

instance Profunctor p => Functor (Tambara p a) where
  fmap = rmap

instance (Profunctor p, Arrow p) => Applicative (Tambara p a) where
  pure x = arr (const x)
  f <*> g = arr (uncurry id) . (f &&& g)

instance (Profunctor p, ArrowPlus p) => Alternative (Tambara p a) where
  empty = zeroArrow
  f <|> g = f <+> g

instance (Profunctor p, ArrowPlus p) => Monoid (Tambara p a b) where
  mempty = zeroArrow
  mappend f g = f <+> g

-- |
-- @
-- 'tambara' '.' 'untambara' ≡ 'id'
-- 'untambara' '.' 'tambara' ≡ 'id'
-- @
tambara :: Strong p => (p -/-> q) -> p -/-> Tambara q
tambara f p = Tambara $ f $ first' p

-- |
-- @
-- 'tambara' '.' 'untambara' ≡ 'id'
-- 'untambara' '.' 'tambara' ≡ 'id'
-- @
untambara :: Profunctor q => (p -/-> Tambara q) -> p -/-> q
untambara f p = dimap (\a -> (a,())) fst $ runTambara $ f p

----------------------------------------------------------------------------
-- * Pastro
----------------------------------------------------------------------------

-- | Pastro -| Tambara
data Pastro p a b where
  Pastro :: ((y, z) -> b) -> p x y -> (a -> (x, z)) -> Pastro p a b

instance Profunctor p => Profunctor (Pastro p) where
  dimap f g (Pastro l m r) = Pastro (g . l) m (r . f)
  lmap f (Pastro l m r) = Pastro l m (r . f)
  rmap g (Pastro l m r) = Pastro (g . l) m r
  w #. Pastro l m r = Pastro (w #. l) m r
  Pastro l m r .# w = Pastro l m (r .# w)

instance ProfunctorMonad Pastro where
  proreturn p = Pastro fst p $ \a -> (a,())
  projoin (Pastro l (Pastro m n o) p) = Pastro lm n op where
    op a = case p a of
      (b, f) -> case o b of
         (c, g) -> (c, (f, g)) 
    lm (d, (f, g)) = l (m (d, g), f)
    
instance ProfunctorAdjunction Pastro Tambara where
  counit (Pastro g (Tambara p) f) = dimap f g p
  unit p = Tambara (Pastro id p id)

----------------------------------------------------------------------------
-- * Cotambara
----------------------------------------------------------------------------

-- | Cotambara is freely adjoins respect for cocartesian structure to a profunctor
newtype Cotambara p a b = Cotambara { runCotambara :: forall c. p (Either a c) (Either b c) }

instance ProfunctorComonad Cotambara where
  proextract (Cotambara p)   = dimap Left (\(Left a) -> a) p
  produplicate (Cotambara p) = Cotambara (Cotambara $ dimap hither yon p) where
    hither (Left (Left x))   = Left x
    hither (Left (Right y))  = Right (Left y)
    hither (Right z)         = Right (Right z)
    yon    (Left x)          = Left (Left x)
    yon    (Right (Left y))  = Left (Right y)
    yon    (Right (Right z)) = Right z

instance Profunctor p => Profunctor (Cotambara p) where
  dimap f g (Cotambara p) = Cotambara $ dimap (left f) (left g) p
  {-# INLINE dimap #-}

instance Profunctor p => Choice (Cotambara p) where
  left' = runCotambara . produplicate
  {-# INLINE left' #-}

instance Category p => Category (Cotambara p) where
  id = Cotambara id
  Cotambara p . Cotambara q = Cotambara (p . q)

instance Profunctor p => Functor (Cotambara p a) where
  fmap = rmap

-- |
-- @
-- 'cotambara' '.' 'uncotambara' ≡ 'id'
-- 'uncotambara' '.' 'cotambara' ≡ 'id'
-- @
cotambara :: Choice p => (p -/-> q) -> p -/-> Cotambara q
cotambara f p = Cotambara $ f $ left' p

-- |
-- @
-- 'cotambara' '.' 'uncotambara' ≡ 'id'
-- 'uncotambara' '.' 'cotambara' ≡ 'id'
-- @
uncotambara :: Profunctor q => (p -/-> Cotambara q) -> p -/-> q
uncotambara f p = dimap Left (\(Left a) -> a) $ runCotambara $ f p

----------------------------------------------------------------------------
-- * Copastro
----------------------------------------------------------------------------

-- | Copastro -| Cotambara
data Copastro p a b where
  Copastro :: (Either y z -> b) -> p x y -> (a -> Either x z) -> Copastro p a b

instance Profunctor p => Profunctor (Copastro p) where
  dimap f g (Copastro l m r) = Copastro (g . l) m (r . f)
  lmap f (Copastro l m r) = Copastro l m (r . f)
  rmap g (Copastro l m r) = Copastro (g . l) m r
  w #. Copastro l m r = Copastro (w #. l) m r
  Copastro l m r .# w = Copastro l m (r .# w)

instance ProfunctorAdjunction Copastro Cotambara where
  counit (Copastro f (Cotambara g) h) = dimap h f g
  unit p = Cotambara $ Copastro id p id

instance ProfunctorMonad Copastro where
  proreturn p = Copastro (\(Left a)-> a) p Left
  projoin (Copastro l (Copastro m n o) q) = Copastro lm n oq where
    oq a = case q a of
      Left b -> case o b of
        Left c -> Left c
        Right z -> Right (Left z)
      Right z -> Right (Right z)
    lm (Left x) = l $ Left $ m $ Left x
    lm (Right (Left y)) = l $ Left $ m $ Right y
    lm (Right (Right z)) = l $ Right z
