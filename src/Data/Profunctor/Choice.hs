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
module Data.Profunctor.Choice
  (
  -- * Strength
    Choice(..)
  , TambaraChoice(..)
  , tambaraChoice, untambaraChoice
  , PastroChoice(..)
  -- * Costrength
  , Cochoice(..)
  , CotambaraChoice(..)
  , cotambaraChoice, uncotambaraChoice
  , CopastroChoice(..)
  ) where

import Control.Applicative hiding (WrappedArrow(..))
import Control.Arrow
import Control.Category
import Control.Comonad
import Data.Bifunctor.Joker (Joker(..))
import Data.Bifunctor.Product (Product(..))
import Data.Bifunctor.Tannen (Tannen(..))
import Data.Monoid hiding (Product)
import Data.Profunctor.Adjunction
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
  left'  :: p a b -> p (Either a c) (Either b c)
  left' =  dimap (either Right Left) (either Right Left) . right'

  right' :: p a b -> p (Either c a) (Either c b)
  right' =  dimap (either Right Left) (either Right Left) . left'

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 708
  {-# MINIMAL left' | right' #-}
#endif

instance Choice (->) where
  left' ab (Left a) = Left (ab a)
  left' _ (Right c) = Right c
  {-# INLINE left' #-}
  right' = fmap
  {-# INLINE right' #-}

instance Monad m => Choice (Kleisli m) where
  left' = left
  {-# INLINE left' #-}
  right' = right
  {-# INLINE right' #-}

instance Applicative f => Choice (Star f) where
  left' (Star f) = Star $ either (fmap Left . f) (pure . Right)
  {-# INLINE left' #-}
  right' (Star f) = Star $ either (pure . Left) (fmap Right . f)
  {-# INLINE right' #-}

-- | 'extract' approximates 'costrength'
instance Comonad w => Choice (Cokleisli w) where
  left' = left
  {-# INLINE left' #-}
  right' = right
  {-# INLINE right' #-}

-- NB: This instance is highly questionable
instance Traversable w => Choice (Costar w) where
  left' (Costar wab) = Costar (either Right Left . fmap wab . traverse (either Right Left))
  {-# INLINE left' #-}
  right' (Costar wab) = Costar (fmap wab . sequence)
  {-# INLINE right' #-}

instance Choice Tagged where
  left' (Tagged b) = Tagged (Left b)
  {-# INLINE left' #-}
  right' (Tagged b) = Tagged (Right b)
  {-# INLINE right' #-}

instance ArrowChoice p => Choice (WrappedArrow p) where
  left' (WrapArrow k) = WrapArrow (left k)
  {-# INLINE left' #-}
  right' (WrapArrow k) = WrapArrow (right k)
  {-# INLINE right' #-}

instance Monoid r => Choice (Forget r) where
  left' (Forget k) = Forget (either k (const mempty))
  {-# INLINE left' #-}
  right' (Forget k) = Forget (either (const mempty) k)
  {-# INLINE right' #-}

instance Functor f => Choice (Joker f) where
  left' (Joker fb) = Joker (fmap Left fb)
  {-# INLINE left' #-}
  right' (Joker fb) = Joker (fmap Right fb)
  {-# INLINE right' #-}

instance (Choice p, Choice q) => Choice (Product p q) where
  left' (Pair p q) = Pair (left' p) (left' q)
  {-# INLINE left' #-}
  right' (Pair p q) = Pair (right' p) (right' q)
  {-# INLINE right' #-}

instance (Functor f, Choice p) => Choice (Tannen f p) where
  left' (Tannen fp) = Tannen (fmap left' fp)
  {-# INLINE left' #-}
  right' (Tannen fp) = Tannen (fmap right' fp)
  {-# INLINE right' #-}

instance Choice p => Choice (Tambara p) where
  left' (Tambara f) = Tambara $ dimap hither yon $ left' f where
    hither :: (Either a b, c) -> Either (a, c) (b, c)
    hither (Left y, s) = Left (y, s)
    hither (Right z, s) = Right (z, s)

    yon :: Either (a, c) (b, c) -> (Either a b, c)
    yon (Left (y, s)) = (Left y, s)
    yon (Right (z, s)) = (Right z, s)


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
