{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Safe #-}

-- |
-- Copyright   : (c) 2014-2015 Edward Kmett
-- License     : BSD-style (see the file LICENSE)
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : Rank2Types

module Data.Profunctor.Choice
(
-- * Strength
  Choice(..)
, splitChoice
, fanIn
, TambaraSum(..)
, tambaraSum, untambaraSum
, PastroSum(..)
-- * Costrength
, Cochoice(..)
, CotambaraSum(..)
, cotambaraSum, uncotambaraSum
, CopastroSum(..)
) where

import Control.Applicative hiding (WrappedArrow(..))
import Control.Arrow
import Control.Category
import Control.Comonad
import Data.Bifunctor.Joker (Joker(..))
import Data.Bifunctor.Product (Product(..))
import Data.Bifunctor.Sum (Sum(..))
import Data.Bifunctor.Tannen (Tannen(..))
import Data.Monoid hiding (Product, Sum)
import Data.Profunctor.Adjunction
import Data.Profunctor.Functor
import Data.Profunctor.Monad
import Data.Profunctor.Strong
import Data.Profunctor.Types
import Data.Profunctor.Unsafe
import Data.Tagged
import Prelude hiding (id,(.))

------------------------------------------------------------------------------
-- Choice
------------------------------------------------------------------------------

-- | The generalization of 'Costar' of 'Functor' that is strong with respect
-- to 'Either'.
--
-- Note: This is also a notion of strength, except with regards to another monoidal
-- structure that we can choose to equip Hask with: the cocartesian coproduct.
class Profunctor p => Choice p where
  -- | Laws:
  --
  -- @
  -- 'left'' ≡ 'dimap' swapE swapE '.' 'right'' where
  --   swapE :: 'Either' a b -> 'Either' b a
  --   swapE = 'either' 'Right' 'Left'
  -- 'rmap' 'Left' ≡ 'lmap' 'Left' '.' 'left''
  -- 'lmap' ('right' f) '.' 'left'' ≡ 'rmap' ('right' f) '.' 'left''
  -- 'left'' '.' 'left'' ≡ 'dimap' assocE unassocE '.' 'left'' where
  --   assocE :: 'Either' ('Either' a b) c -> 'Either' a ('Either' b c)
  --   assocE ('Left' ('Left' a)) = 'Left' a
  --   assocE ('Left' ('Right' b)) = 'Right' ('Left' b)
  --   assocE ('Right' c) = 'Right' ('Right' c)
  --   unassocE :: 'Either' a ('Either' b c) -> 'Either' ('Either' a b) c
  --   unassocE ('Left' a) = 'Left' ('Left' a)
  --   unassocE ('Right' ('Left' b)) = 'Left' ('Right' b)
  --   unassocE ('Right' ('Right' c)) = 'Right' c
  -- @
  left'  :: p a b -> p (Either a c) (Either b c)
  left' = dimap (either Right Left) (either Right Left) . right'
  {-# inline left' #-}

  -- | Laws:
  --
  -- @
  -- 'right'' ≡ 'dimap' swapE swapE '.' 'left'' where
  --   swapE :: 'Either' a b -> 'Either' b a
  --   swapE = 'either' 'Right' 'Left'
  -- 'rmap' 'Right' ≡ 'lmap' 'Right' '.' 'right''
  -- 'lmap' ('left' f) '.' 'right'' ≡ 'rmap' ('left' f) '.' 'right''
  -- 'right'' '.' 'right'' ≡ 'dimap' unassocE assocE '.' 'right'' where
  --   assocE :: 'Either' ('Either' a b) c -> 'Either' a ('Either' b c)
  --   assocE ('Left' ('Left' a)) = 'Left' a
  --   assocE ('Left' ('Right' b)) = 'Right' ('Left' b)
  --   assocE ('Right' c) = 'Right' ('Right' c)
  --   unassocE :: 'Either' a ('Either' b c) -> 'Either' ('Either' a b) c
  --   unassocE ('Left' a) = 'Left' ('Left' a)
  --   unassocE ('Right' ('Left' b)) = 'Left' ('Right' b)
  --   unassocE ('Right' ('Right' c)) = 'Right' c
  -- @
  right' :: p a b -> p (Either c a) (Either c b)
  right' = dimap (either Right Left) (either Right Left) . left'
  {-# inline right' #-}

  {-# MINIMAL left' | right' #-}

splitChoice :: (Category p, Choice p) => p a b -> p c d -> p (Either a c) (Either b d)
splitChoice l r = left' l . right' r
{-# INLINE splitChoice #-}

fanIn :: (Category p, Choice p) => p a c -> p b c -> p (Either a b) c
fanIn l r = lmap (either id id) id . splitChoice l r
{-# INLINE fanIn #-}

instance Choice (->) where
  left' = \ab -> \case
    Left a -> Left (ab a)
    Right c -> Right c
  {-# inline left' #-}
  right' = fmap
  {-# inline right' #-}

instance Monad m => Choice (Kleisli m) where
  left' = left
  {-# inline left' #-}
  right' = right
  {-# inline right' #-}

instance Applicative f => Choice (Star f) where
  left' = \(Star f) -> Star $ either (fmap Left . f) (pure . Right)
  {-# inline left' #-}
  right' = \(Star f) -> Star $ either (pure . Left) (fmap Right . f)
  {-# inline right' #-}

-- this actually needs a linear- "control" functor in the linear-haskell sense

-- | 'extract' approximates 'costrength'
instance Comonad w => Choice (Cokleisli w) where
  left' = left
  {-# inline left' #-}
  right' = right
  {-# inline right' #-}

instance Choice Tagged where
  left'  = \(Tagged b) -> Tagged (Left b)
  {-# inline left' #-}
  right' = \(Tagged b) -> Tagged (Right b)
  {-# inline right' #-}

instance ArrowChoice p => Choice (WrappedArrow p) where
  left' = \(WrapArrow k) -> WrapArrow (left k)
  {-# inline left' #-}
  right' = \(WrapArrow k) -> WrapArrow (right k)
  {-# inline right' #-}

instance Monoid r => Choice (Forget r) where
  left' = \(Forget k) -> Forget (either k (const mempty))
  {-# inline left' #-}
  right' = \(Forget k) -> Forget (either (const mempty) k)
  {-# inline right' #-}

instance Functor f => Choice (Joker f) where
  left' = \(Joker fb) -> Joker (fmap Left fb)
  {-# inline left' #-}
  right' = \(Joker fb) -> Joker (fmap Right fb)
  {-# inline right' #-}

instance (Choice p, Choice q) => Choice (Product p q) where
  left' = \(Pair p q) -> Pair (left' p) (left' q)
  {-# inline left' #-}
  right' = \(Pair p q) -> Pair (right' p) (right' q)
  {-# inline right' #-}

instance (Choice p, Choice q) => Choice (Sum p q) where
  left' = \case
    L2 p -> L2 (left' p)
    R2 q -> R2 (left' q)
  {-# inline left' #-}
  right' = \case
    L2 p -> L2 (right' p)
    R2 q -> R2 (right' q)
  {-# inline right' #-}

instance (Functor f, Choice p) => Choice (Tannen f p) where
  left' = \(Tannen fp) -> Tannen (fmap left' fp)
  {-# inline left' #-}
  right' = \(Tannen fp) -> Tannen (fmap right' fp)
  {-# inline right' #-}

instance Choice p => Choice (Tambara p) where
  left' = \ (Tambara f) -> let
      hither :: (Either a b, c) -> Either (a, c) (b, c)
      hither = \case
        (Left y, s) -> Left (y, s)
        (Right z, s) -> Right (z, s)
  
      yon :: Either (a, c) (b, c) -> (Either a b, c)
      yon = \case
        Left (y, s) -> (Left y, s)
        Right (z, s) -> (Right z, s)
    in Tambara $ dimap hither yon $ left' f
  {-# inline left' #-}


----------------------------------------------------------------------------
-- * TambaraSum
----------------------------------------------------------------------------

-- | TambaraSum is cofreely adjoins strength with respect to Either.
--
-- Note: this is not dual to 'Data.Profunctor.Tambara.Tambara'. It is 'Data.Profunctor.Tambara.Tambara' with respect to a different tensor.
newtype TambaraSum p a b = TambaraSum
  { runTambaraSum :: forall c. p (Either a c) (Either b c)
  }

instance ProfunctorFunctor TambaraSum where
  promap = \f g -> TambaraSum (f (runTambaraSum g))
  {-# inline promap #-}

instance ProfunctorComonad TambaraSum where
  proextract = \(TambaraSum p) -> dimap Left fromEither p
  {-# inline proextract #-}
  produplicate = \(TambaraSum p) -> let
      hither :: Either (Either a b) c -> Either a (Either b c)
      hither (Left (Left x))   = Left x
      hither (Left (Right y))  = Right (Left y)
      hither (Right z)         = Right (Right z)
  
      yon    :: Either a (Either b c) -> Either (Either a b) c
      yon    (Left x)          = Left (Left x)
      yon    (Right (Left y))  = Left (Right y)
      yon    (Right (Right z)) = Right z
    in TambaraSum (TambaraSum $ dimap hither yon p)
  {-# inline produplicate #-}

instance Profunctor p => Profunctor (TambaraSum p) where
  dimap = \f g (TambaraSum p) -> TambaraSum $ dimap (left f) (left g) p
  {-# inline dimap #-}

instance Profunctor p => Choice (TambaraSum p) where
  left' = \p -> runTambaraSum $ produplicate p
  {-# inline left' #-}

instance Category p => Category (TambaraSum p) where
  id = TambaraSum id
  (.) = \(TambaraSum p) (TambaraSum q) -> TambaraSum (p . q)
  {-# inline (.) #-}

instance Profunctor p => Functor (TambaraSum p a) where
  fmap = rmap

-- |
-- @
-- 'tambaraSum' '.' 'untambaraSum' ≡ 'id'
-- 'untambaraSum' '.' 'tambaraSum' ≡ 'id'
-- @
tambaraSum :: Choice p => (p :-> q) -> p :-> TambaraSum q
tambaraSum = \f p -> TambaraSum $ f $ left' p
{-# inline tambaraSum #-}

-- |
-- @
-- 'tambaraSum' '.' 'untambaraSum' ≡ 'id'
-- 'untambaraSum' '.' 'tambaraSum' ≡ 'id'
-- @
untambaraSum :: Profunctor q => (p :-> TambaraSum q) -> p :-> q
untambaraSum = \f p -> dimap Left fromEither $ runTambaraSum $ f p
{-# inline untambaraSum #-}

fromEither :: Either a a -> a
fromEither = either id id

----------------------------------------------------------------------------
-- * PastroSum
----------------------------------------------------------------------------

-- | PastroSum -| TambaraSum
--
-- PastroSum freely constructs strength with respect to Either.
data PastroSum p a b where
  PastroSum :: (Either y z -> b) -> p x y -> (a -> Either x z) -> PastroSum p a b

instance Functor (PastroSum p a) where
  fmap = \f (PastroSum l m r) -> PastroSum (f . l) m r
  {-# inline fmap #-}

instance Profunctor (PastroSum p) where
  dimap = \f g (PastroSum l m r) -> PastroSum (g . l) m (r . f)
  lmap = \f (PastroSum l m r) -> PastroSum l m (r . f)
  rmap = \g (PastroSum l m r) -> PastroSum (g . l) m r
  (#.) = \w (PastroSum l m r) -> PastroSum (w #. l) m r
  (.#) = \(PastroSum l m r) w -> PastroSum l m (r .# w)

instance ProfunctorAdjunction PastroSum TambaraSum where
  counit = \(PastroSum f (TambaraSum g) h) -> dimap h f g
  {-# inline counit #-}
  unit = \p -> TambaraSum $ PastroSum id p id
  {-# inline unit #-}

instance ProfunctorFunctor PastroSum where
  promap = \f (PastroSum l m r) -> PastroSum l (f m) r
  {-# inline promap #-}

instance ProfunctorMonad PastroSum where
  proreturn = \p -> PastroSum fromEither p Left
  projoin = \(PastroSum l (PastroSum m n o) q) ->
    let 
      oq a = case q a of
        Left b -> Left <$> o b
        Right z -> Right (Right z)
      lm (Left x) = l $ Left $ m $ Left x
      lm (Right (Left y)) = l $ Left $ m $ Right y
      lm (Right (Right z)) = l $ Right z
    in PastroSum lm n oq

instance Choice (PastroSum p) where
  left' = \(PastroSum l m r) -> let
      r' = either (fmap Left . r) (Right . Right)
      l' (Left y)          = Left (l (Left y))
      l' (Right (Left z))  = Left (l (Right z))
      l' (Right (Right c)) = Right c
    in PastroSum l' m r'
  right' = \(PastroSum l m r) -> let 
      r' = either (Right . Left) (fmap Right . r)
      l' (Right (Left c))  = Left c
      l' (Right (Right z)) = Right (l (Right z))
      l' (Left y)          = Right (l (Left y))
    in PastroSum l' m r'

--------------------------------------------------------------------------------
-- * Costrength for Either
--------------------------------------------------------------------------------

class Profunctor p => Cochoice p where
  -- | Laws:
  --
  -- @
  -- 'unleft' ≡ 'unright' '.' 'dimap' swapE swapE where
  --   swapE :: 'Either' a b -> 'Either' b a
  --   swapE = 'either' 'Right' 'Left'
  -- 'rmap' ('either' 'id' 'absurd') ≡ 'unleft' '.' 'lmap' ('either' 'id' 'absurd')
  -- 'unleft' '.' 'rmap' ('right' f) ≡ 'unleft' '.' 'lmap' ('right' f)
  -- 'unleft' '.' 'unleft' ≡ 'unleft' '.' 'dimap' unassocE assocE where
  --   assocE :: 'Either' ('Either' a b) c -> 'Either' a ('Either' b c)
  --   assocE ('Left' ('Left' a)) = 'Left' a
  --   assocE ('Left' ('Right' b)) = 'Right' ('Left' b)
  --   assocE ('Right' c) = 'Right' ('Right' c)
  --   unassocE :: 'Either' a ('Either' b c) -> 'Either' ('Either' a b) c
  --   unassocE ('Left' a) = 'Left' ('Left' a)
  --   unassocE ('Right' ('Left' b)) = 'Left' ('Right' b)
  --   unassocE ('Right' ('Right' c)) = 'Right' c
  -- @
  unleft  :: p (Either a d) (Either b d) -> p a b
  unleft = unright . dimap (either Right Left) (either Right Left)
  {-# inline unleft #-}

  -- | Laws:
  --
  -- @
  -- 'unright' ≡ 'unleft' '.' 'dimap' swapE swapE where
  --   swapE :: 'Either' a b -> 'Either' b a
  --   swapE = 'either' 'Right' 'Left'
  -- 'rmap' ('either' 'absurd' 'id') ≡ 'unright' '.' 'lmap' ('either' 'absurd' 'id')
  -- 'unright' '.' 'rmap' ('left' f) ≡ 'unright' '.' 'lmap' ('left' f)
  -- 'unright' '.' 'unright' ≡ 'unright' '.' 'dimap' assocE unassocE where
  --   assocE :: 'Either' ('Either' a b) c -> 'Either' a ('Either' b c)
  --   assocE ('Left' ('Left' a)) = 'Left' a
  --   assocE ('Left' ('Right' b)) = 'Right' ('Left' b)
  --   assocE ('Right' c) = 'Right' ('Right' c)
  --   unassocE :: 'Either' a ('Either' b c) -> 'Either' ('Either' a b) c
  --   unassocE ('Left' a) = 'Left' ('Left' a)
  --   unassocE ('Right' ('Left' b)) = 'Left' ('Right' b)
  --   unassocE ('Right' ('Right' c)) = 'Right' c
  -- @
  unright :: p (Either d a) (Either d b) -> p a b
  unright = unleft . dimap (either Right Left) (either Right Left)
  {-# inline unright #-}

  {-# MINIMAL unleft | unright #-}

instance Cochoice (->) where
  unleft = \f -> let go = either id (go . Right) . f in go . Left
  {-# inline unleft #-}
  unright = \f -> let go = either (go . Left) id . f in go . Right
  {-# inline unright #-}

{-
instance Applicative f => Cochoice (Costar f) where
  unleft (Costar f) = Costar (go . fmap Left)
    where go = either id (go . pure . Right) . f
-}

-- NB: Another instance that's highly questionable
instance Traversable f => Cochoice (Star f) where
  unright = \(Star f) -> let go = either (go . Left) id . sequence . f in Star (go . Right)
  {-# inline unright #-}

instance (Functor f, Cochoice p) => Cochoice (Tannen f p) where
  unleft (Tannen fp) = Tannen (fmap unleft fp)
  {-# inline unleft #-}
  unright (Tannen fp) = Tannen (fmap unright fp)
  {-# inline unright #-}

instance (Cochoice p, Cochoice q) => Cochoice (Product p q) where
  unleft = \(Pair p q) -> Pair (unleft p) (unleft q)
  {-# inline unleft #-}
  unright = \(Pair p q) -> Pair (unright p) (unright q)
  {-# inline unright #-}

instance (Cochoice p, Cochoice q) => Cochoice (Sum p q) where
  unleft = \case
    L2 p -> L2 (unleft p)
    R2 q -> R2 (unleft q)
  {-# inline unleft #-}
  unright = \case
    L2 p -> L2 (unright p)
    R2 q -> R2 (unright q)
  {-# inline unright #-}

instance Cochoice (Forget r) where
  unleft = \(Forget f) -> Forget (f . Left)
  {-# inline unleft #-}
  unright = \(Forget f) -> Forget (f . Right)
  {-# inline unright #-}

----------------------------------------------------------------------------
-- * CotambaraSum
----------------------------------------------------------------------------

-- | 'CotambaraSum' cofreely constructs costrength with respect to 'Either' (aka 'Choice')
data CotambaraSum q a b where
    CotambaraSum :: Cochoice r => (r :-> q) -> r a b -> CotambaraSum q a b

instance Profunctor (CotambaraSum p) where
  lmap = \f (CotambaraSum n p) -> CotambaraSum n (lmap f p)
  rmap = \g (CotambaraSum n p) -> CotambaraSum n (rmap g p)
  dimap = \f g (CotambaraSum n p) -> CotambaraSum n (dimap f g p)
  {-# inline lmap #-}
  {-# inline rmap #-}
  {-# inline dimap #-}

instance ProfunctorFunctor CotambaraSum where
  promap = \f (CotambaraSum n p) -> CotambaraSum (f . n) p
  {-# inline promap #-}

instance ProfunctorComonad CotambaraSum where
  proextract = \(CotambaraSum n p) -> n p
  {-# inline proextract #-}
  produplicate = \(CotambaraSum n p) -> CotambaraSum id (CotambaraSum n p)
  {-# inline produplicate #-}

instance Cochoice (CotambaraSum p) where
  unleft = \(CotambaraSum n p) -> CotambaraSum n (unleft p)
  {-# inline unleft #-}
  unright = \(CotambaraSum n p) -> CotambaraSum n (unright p)
  {-# inline unright #-}

instance Functor (CotambaraSum p a) where
  fmap = rmap
  {-# inline fmap #-}

-- |
-- @
-- 'cotambaraSum' '.' 'uncotambaraSum' ≡ 'id'
-- 'uncotambaraSum' '.' 'cotambaraSum' ≡ 'id'
-- @
cotambaraSum :: Cochoice p => (p :-> q) -> p :-> CotambaraSum q
cotambaraSum = \f -> CotambaraSum f
{-# inline cotambaraSum #-}

-- |
-- @
-- 'cotambaraSum' '.' 'uncotambaraSum' ≡ 'id'
-- 'uncotambaraSum' '.' 'cotambaraSum' ≡ 'id'
-- @
uncotambaraSum :: Profunctor q => (p :-> CotambaraSum q) -> p :-> q
uncotambaraSum = \f p -> proextract (f p)
{-# inline uncotambaraSum #-}

----------------------------------------------------------------------------
-- * Copastro
----------------------------------------------------------------------------

-- | CopastroSum -| CotambaraSum
--
-- 'CopastroSum' freely constructs costrength with respect to 'Either' (aka 'Choice')
newtype CopastroSum p a b = CopastroSum
  { runCopastroSum :: forall r. Cochoice r => (forall x y. p x y -> r x y) -> r a b
  }

instance Functor (CopastroSum p a) where
  fmap = \f (CopastroSum h) -> CopastroSum $ \ n -> rmap f (h n)
  {-# inline fmap #-}

instance Profunctor (CopastroSum p) where
  dimap = \f g (CopastroSum h) -> CopastroSum $ \ n -> dimap f g (h n)
  lmap = \f (CopastroSum h) -> CopastroSum $ \ n -> lmap f (h n)
  rmap = \g (CopastroSum h) -> CopastroSum $ \ n -> rmap g (h n)
  {-# inline dimap #-}
  {-# inline lmap #-}
  {-# inline rmap #-}

instance ProfunctorAdjunction CopastroSum CotambaraSum where
  unit = \p -> CotambaraSum id (proreturn p)
  {-# inline unit #-}
  counit = \(CopastroSum h) -> proextract (h id)
  {-# inline counit #-}

instance ProfunctorFunctor CopastroSum where
  promap = \f (CopastroSum h) -> CopastroSum $ \n -> h (n . f)
  {-# inline promap #-}

instance ProfunctorMonad CopastroSum where
  proreturn = \p -> CopastroSum $ \n -> n p
  {-# inline proreturn #-}
  projoin = \p -> CopastroSum $ \c -> runCopastroSum p (\x -> runCopastroSum x c)
  {-# inline projoin #-}

instance Cochoice (CopastroSum p) where
  unleft = \(CopastroSum p) -> CopastroSum $ \n -> unleft (p n)
  {-# inline unleft #-}
  unright = \(CopastroSum p) -> CopastroSum $ \n -> unright (p n)
  {-# inline unright #-}
