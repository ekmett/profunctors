{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}

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
module Data.Profunctor.Strong
  (
  -- * Strength
    Strong(..)
  , uncurry'
  , strong
  , Tambara(..)
  , tambara, untambara
  , Pastro(..)
  , pastro, unpastro
  -- * Costrength
  , Costrong(..)
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
import Data.Bifunctor.Clown (Clown(..))
import Data.Bifunctor.Product (Product(..))
import Data.Bifunctor.Sum (Sum(..))
import Data.Bifunctor.Tannen (Tannen(..))
import Data.Functor.Contravariant (Contravariant(..))
import Data.Profunctor.Adjunction
import Data.Profunctor.Monad
import Data.Profunctor.Types
import Data.Profunctor.Unsafe
import Data.Semigroup hiding (Product, Sum)
import Data.Tagged
import Data.Tuple
import Prelude hiding (id,(.))

------------------------------------------------------------------------------
-- Strong
------------------------------------------------------------------------------

-- | Generalizing 'Star' of a strong 'Functor'
--
-- /Note:/ Every 'Functor' in Haskell is strong with respect to @(,)@.
--
-- This describes profunctor strength with respect to the product structure
-- of Hask.
--
-- <http://www.riec.tohoku.ac.jp/~asada/papers/arrStrMnd.pdf>
--
class Profunctor p => Strong p where
  -- | Laws:
  --
  -- @
  -- 'first'' ≡ 'dimap' 'swap' 'swap' '.' 'second''
  -- 'lmap' 'fst' ≡ 'rmap' 'fst' '.' 'first''
  -- 'lmap' ('second'' f) '.' 'first'' ≡ 'rmap' ('second'' f) '.' 'first''
  -- 'first'' '.' 'first'' ≡ 'dimap' assoc unassoc '.' 'first'' where
  --   assoc ((a,b),c) = (a,(b,c))
  --   unassoc (a,(b,c)) = ((a,b),c)
  -- @
  first' :: p a b  -> p (a, c) (b, c)
  first' = dimap swap swap . second'

  -- | Laws:
  --
  -- @
  -- 'second'' ≡ 'dimap' 'swap' 'swap' '.' 'first''
  -- 'lmap' 'snd' ≡ 'rmap' 'snd' '.' 'second''
  -- 'lmap' ('first'' f) '.' 'second'' ≡ 'rmap' ('first'' f) '.' 'second''
  -- 'second'' '.' 'second'' ≡ 'dimap' unassoc assoc '.' 'second'' where
  --   assoc ((a,b),c) = (a,(b,c))
  --   unassoc (a,(b,c)) = ((a,b),c)
  -- @
  second' :: p a b -> p (c, a) (c, b)
  second' = dimap swap swap . first'

  {-# MINIMAL first' | second' #-}

uncurry' :: Strong p => p a (b -> c) -> p (a, b) c
uncurry' = rmap (\(f,x) -> f x) . first'
{-# INLINE uncurry' #-}

strong :: Strong p => (a -> b -> c) -> p a b -> p a c
strong f x = dimap (\a -> (a, a)) (\(b, a) -> f a b) (first' x)

instance Strong (->) where
  first' ab ~(a, c) = (ab a, c)
  {-# INLINE first' #-}
  second' ab ~(c, a) = (c, ab a)
  {-# INLINE second' #-}

instance Monad m => Strong (Kleisli m) where
  first' (Kleisli f) = Kleisli $ \ ~(a, c) -> do
     b <- f a
     return (b, c)
  {-# INLINE first' #-}
  second' (Kleisli f) = Kleisli $ \ ~(c, a) -> do
     b <- f a
     return (c, b)
  {-# INLINE second' #-}

instance Functor m => Strong (Star m) where
  first' (Star f) = Star $ \ ~(a, c) -> (\b' -> (b', c)) <$> f a
  {-# INLINE first' #-}
  second' (Star f) = Star $ \ ~(c, a) -> (,) c <$> f a
  {-# INLINE second' #-}

-- | 'Arrow' is 'Strong' 'Category'
instance Arrow p => Strong (WrappedArrow p) where
  first' (WrapArrow k) = WrapArrow (first k)
  {-# INLINE first' #-}
  second' (WrapArrow k) = WrapArrow (second k)
  {-# INLINE second' #-}

instance Strong (Forget r) where
  first' (Forget k) = Forget (k . fst)
  {-# INLINE first' #-}
  second' (Forget k) = Forget (k . snd)
  {-# INLINE second' #-}

instance Contravariant f => Strong (Clown f) where
  first' (Clown fa) = Clown (contramap fst fa)
  {-# INLINE first' #-}
  second' (Clown fa) = Clown (contramap snd fa)
  {-# INLINE second' #-}

instance (Strong p, Strong q) => Strong (Product p q) where
  first' (Pair p q) = Pair (first' p) (first' q)
  {-# INLINE first' #-}
  second' (Pair p q) = Pair (second' p) (second' q)
  {-# INLINE second' #-}

instance (Strong p, Strong q) => Strong (Sum p q) where
  first' (L2 p) = L2 (first' p)
  first' (R2 q) = R2 (first' q)
  {-# INLINE first' #-}
  second' (L2 p) = L2 (second' p)
  second' (R2 q) = R2 (second' q)
  {-# INLINE second' #-}

instance (Functor f, Strong p) => Strong (Tannen f p) where
  first' (Tannen fp) = Tannen (fmap first' fp)
  {-# INLINE first' #-}
  second' (Tannen fp) = Tannen (fmap second' fp)
  {-# INLINE second' #-}

----------------------------------------------------------------------------
-- * Tambara
----------------------------------------------------------------------------

-- | 'Tambara' cofreely makes any 'Profunctor' 'Strong'.
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
  first' p = runTambara $ produplicate p
  {-# INLINE first' #-}

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

instance ArrowPlus p => Semigroup (Tambara p a b) where
  f <> g = f <+> g

instance ArrowPlus p => Monoid (Tambara p a b) where
  mempty = zeroArrow
#if !(MIN_VERSION_base(4,11,0))
  mappend = (<>)
#endif

-- |
-- @
-- 'tambara' ('untambara' f) ≡ f
-- 'untambara' ('tambara' f) ≡ f
-- @
tambara :: Strong p => (p :-> q) -> p :-> Tambara q
tambara f p = Tambara $ f $ first' p

-- |
-- @
-- 'tambara' ('untambara' f) ≡ f
-- 'untambara' ('tambara' f) ≡ f
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
--
-- 'Pastro' freely makes any 'Profunctor' 'Strong'.
data Pastro p a b where
  Pastro :: ((y, z) -> b) -> p x y -> (a -> (x, z)) -> Pastro p a b

instance Profunctor (Pastro p) where
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

instance Strong (Pastro p) where
  first' (Pastro l m r) = Pastro l' m r' where
    r' (a,c) = case r a of
      (x,z) -> (x,(z,c))
    l' (y,(z,c)) = (l (y,z), c)
  second' (Pastro l m r) = Pastro l' m r' where
    r' (c,a) = case r a of
      (x,z) -> (x,(c,z))
    l' (y,(c,z)) = (c,l (y,z))

-- |
-- @
-- 'pastro' ('unpastro' f) ≡ f
-- 'unpastro' ('pastro' f) ≡ f
-- @
pastro :: Strong q => (p :-> q) -> Pastro p :-> q
pastro f (Pastro r g l) = dimap l r (first' (f g))

-- |
-- @
-- 'pastro' ('unpastro' f) ≡ f
-- 'unpastro' ('pastro' f) ≡ f
-- @
unpastro :: (Pastro p :-> q) -> p :-> q
unpastro f p = f (Pastro fst p (\a -> (a, ())))

--------------------------------------------------------------------------------
-- * Costrength for (,)
--------------------------------------------------------------------------------

-- | Analogous to 'ArrowLoop', 'loop' = 'unfirst'
class Profunctor p => Costrong p where
  -- | Laws:
  --
  -- @
  -- 'unfirst' ≡ 'unsecond' '.' 'dimap' 'swap' 'swap'
  -- 'lmap' (,()) ≡ 'unfirst' '.' 'rmap' (,())
  -- 'unfirst' '.' 'lmap' ('second' f) ≡ 'unfirst' '.' 'rmap' ('second' f)
  -- 'unfirst' '.' 'unfirst' = 'unfirst' '.' 'dimap' assoc unassoc where
  --   assoc ((a,b),c) = (a,(b,c))
  --   unassoc (a,(b,c)) = ((a,b),c)
  -- @
  unfirst  :: p (a, d) (b, d) -> p a b
  unfirst = unsecond . dimap swap swap

  -- | Laws:
  --
  -- @
  -- 'unsecond' ≡ 'unfirst' '.' 'dimap' 'swap' 'swap'
  -- 'lmap' ((),) ≡ 'unsecond' '.' 'rmap' ((),)
  -- 'unsecond' '.' 'lmap' ('first' f) ≡ 'unsecond' '.' 'rmap' ('first' f)
  -- 'unsecond' '.' 'unsecond' = 'unsecond' '.' 'dimap' unassoc assoc where
  --   assoc ((a,b),c) = (a,(b,c))
  --   unassoc (a,(b,c)) = ((a,b),c)
  -- @
  unsecond :: p (d, a) (d, b) -> p a b
  unsecond = unfirst . dimap swap swap

  {-# MINIMAL unfirst | unsecond #-}

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

instance (Costrong p, Costrong q) => Costrong (Sum p q) where
  unfirst (L2 p) = L2 (unfirst p)
  unfirst (R2 q) = R2 (unfirst q)
  unsecond (L2 p) = L2 (unsecond p)
  unsecond (R2 q) = R2 (unsecond q)

----------------------------------------------------------------------------
-- * Cotambara
----------------------------------------------------------------------------

-- | Cotambara cofreely constructs costrength
data Cotambara q a b where
    Cotambara :: Costrong r => (r :-> q) -> r a b -> Cotambara q a b

instance Profunctor (Cotambara p) where
  lmap f (Cotambara n p) = Cotambara n (lmap f p)
  rmap g (Cotambara n p) = Cotambara n (rmap g p)
  dimap f g (Cotambara n p) = Cotambara n (dimap f g p)

instance ProfunctorFunctor Cotambara where
  promap f (Cotambara n p) = Cotambara (f . n) p

instance ProfunctorComonad Cotambara where
  proextract (Cotambara n p)  = n p
  produplicate (Cotambara n p) = Cotambara id (Cotambara n p)

instance Costrong (Cotambara p) where
  unfirst (Cotambara n p) = Cotambara n (unfirst p)

instance Functor (Cotambara p a) where
  fmap = rmap

-- |
-- @
-- 'cotambara' '.' 'uncotambara' ≡ 'id'
-- 'uncotambara' '.' 'cotambara' ≡ 'id'
-- @
cotambara :: Costrong p => (p :-> q) -> p :-> Cotambara q
cotambara f = Cotambara f

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
newtype Copastro p a b = Copastro { runCopastro :: forall r. Costrong r => (forall x y. p x y -> r x y) -> r a b }

instance Profunctor (Copastro p) where
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

instance Costrong (Copastro p) where
  unfirst (Copastro p) = Copastro $ \n -> unfirst (p n)
  unsecond (Copastro p) = Copastro $ \n -> unsecond (p n)
