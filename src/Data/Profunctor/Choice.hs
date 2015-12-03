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
  ( Choice(..)
  , TambaraChoice(..)
  , tambaraChoice, untambaraChoice
  , PastroChoice(..)
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

