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

instance ProfunctorFunctor Tambara where
  promap f (Tambara p) = Tambara (f p)

instance ProfunctorComonad Tambara where
  proextract (Tambara p) = dimap (\a -> (a,())) fst p
  produplicate (Tambara p) = Tambara (Tambara $ dimap hither yon p) where
    hither :: ((a, b), c) -> (a, (b, c))
    hither ~(~(x,y),z) = (x,(y,z))

    yon    :: (a, (b, c)) -> ((a, b), c)
    yon    ~(x,~(y,z)) = ((x,y),z)

instance Profunctor p => Strong (Tambara p) where
  first' = runTambara . produplicate
  {-# INLINE first' #-}

instance Choice p => Choice (Tambara p) where
  left' (Tambara f) = Tambara $ dimap hither yon $ left' f where
    hither :: (Either a b, c) -> Either (a, c) (b, c)
    hither (Left y, s) = Left (y, s)
    hither (Right z, s) = Right (z, s)

    yon :: Either (a, c) (b, c) -> (Either a b, c)
    yon (Left (y, s)) = (Left y, s)
    yon (Right (z, s)) = (Right z, s)

instance Category p => Category (Tambara p) where
  id = Tambara id
  Tambara p . Tambara q = Tambara (p . q)

instance Arrow p => Arrow (Tambara p) where
  arr f = Tambara $ arr $ first f
  first (Tambara f) = Tambara (arr go . first f . arr go) where
    go :: ((a, b), c) -> ((a, c), b)
    go ~(~(x,y),z) = ((x,z),y)

instance ArrowChoice p => ArrowChoice (Tambara p) where
  left (Tambara f) = Tambara (arr yon . left f . arr hither) where
    hither :: (Either a b, c) -> Either (a, c) (b, c)
    hither (Left y, s) = Left (y, s)
    hither (Right z, s) = Right (z, s)

    yon :: Either (a, c) (b, c) -> (Either a b, c)
    yon (Left (y, s)) = (Left y, s)
    yon (Right (z, s)) = (Right z, s)

instance ArrowApply p => ArrowApply (Tambara p) where
  app = Tambara $ app . arr (\((Tambara f, x), s) -> (f, (x, s)))

instance ArrowLoop p => ArrowLoop (Tambara p) where
  loop (Tambara f) = Tambara (loop (arr go . f . arr go)) where
    go :: ((a, b), c) -> ((a, c), b)
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
tambara :: Strong p => (p :-> q) -> p :-> Tambara q
tambara f p = Tambara $ f $ first' p

-- |
-- @
-- 'tambara' '.' 'untambara' ≡ 'id'
-- 'untambara' '.' 'tambara' ≡ 'id'
-- @
untambara :: Profunctor q => (p :-> Tambara q) -> p :-> q
untambara f p = dimap (\a -> (a,())) fst $ runTambara $ f p

----------------------------------------------------------------------------
-- * Pastro
----------------------------------------------------------------------------

-- | Pastro -| Tambara
--
-- @
-- Pastro p ~ exists z. Costar ((,)z) `Procompose` p `Procompose` Star ((,)z)
-- @
data Pastro p a b where
  Pastro :: ((y, z) -> b) -> p x y -> (a -> (x, z)) -> Pastro p a b

instance Profunctor p => Profunctor (Pastro p) where
  dimap f g (Pastro l m r) = Pastro (g . l) m (r . f)
  lmap f (Pastro l m r) = Pastro l m (r . f)
  rmap g (Pastro l m r) = Pastro (g . l) m r
  w #. Pastro l m r = Pastro (w #. l) m r
  Pastro l m r .# w = Pastro l m (r .# w)

instance ProfunctorFunctor Pastro where
  promap f (Pastro l m r) = Pastro l (f m) r

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
