{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
module Data.Profunctor.Traversing
  ( Traversing(..)
  , CofreeTraversing(..)
  , FreeTraversing(..)
  -- * Profunctor in terms of Traversing
  , dimapWandering
  , lmapWandering
  , rmapWandering
  -- * Strong in terms of Traversing
  , firstTraversing
  , secondTraversing
  -- * Choice in terms of Traversing
  , leftTraversing
  , rightTraversing
  ) where

import Control.Applicative
import Control.Arrow (Kleisli(..))
import Data.Bifunctor.Tannen
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Orphans ()
import Data.Profunctor.Choice
import Data.Profunctor.Monad
import Data.Profunctor.Strong
import Data.Profunctor.Types
import Data.Profunctor.Unsafe
import Data.Traversable
import Data.Tuple (swap)

#if __GLASGOW_HASKELL__ < 710
import Data.Monoid (Monoid)
import Data.Foldable
import Prelude hiding (mapM)
#endif

firstTraversing :: Traversing p => p a b -> p (a, c) (b, c)
firstTraversing = dimap swap swap . traverse'

secondTraversing :: Traversing p => p a b -> p (c, a) (c, b)
secondTraversing = traverse'

swapE :: Either a b -> Either b a
swapE = either Right Left

-- | A definition of 'dimap' for 'Traversing' instances that define
-- an explicit 'wander'.
dimapWandering :: Traversing p => (a' -> a) -> (b -> b') -> p a b -> p a' b'
dimapWandering f g = wander (\afb a' -> g <$> afb (f a'))

-- | 'lmapWandering' may be a more efficient implementation
-- of 'lmap' than the default produced from 'dimapWandering'.
lmapWandering :: Traversing p => (a -> b) -> p b c -> p a c
lmapWandering f = wander (\afb a' -> afb (f a'))

-- | 'rmapWandering' is the same as the default produced from
-- 'dimapWandering'.
rmapWandering :: Traversing p => (b -> c) -> p a b -> p a c
rmapWandering g = wander (\afb a' -> g <$> afb a')

leftTraversing :: Traversing p => p a b -> p (Either a c) (Either b c)
leftTraversing = dimap swapE swapE . traverse'

rightTraversing :: Traversing p => p a b -> p (Either c a) (Either c b)
rightTraversing = traverse'

newtype Bazaar a b t = Bazaar { runBazaar :: forall f. Applicative f => (a -> f b) -> f t }
  deriving Functor

instance Applicative (Bazaar a b) where
  pure a = Bazaar $ \_ -> pure a
  mf <*> ma = Bazaar $ \k -> runBazaar mf k <*> runBazaar ma k

instance Profunctor (Bazaar a) where
  dimap f g m = Bazaar $ \k -> g <$> runBazaar m (fmap f . k)

sell :: a -> Bazaar a b b
sell a = Bazaar $ \k -> k a

newtype Baz t b a = Baz { runBaz :: forall f. Applicative f => (a -> f b) -> f t }
  deriving Functor

-- bsell :: a -> Baz b b a
-- bsell a = Baz $ \k -> k a

-- aar :: Bazaar a b t -> Baz t b a
-- aar (Bazaar f) = Baz f

sold :: Baz t a a -> t
sold m = runIdentity (runBaz m Identity)

instance Foldable (Baz t b) where
  foldMap = foldMapDefault

instance Traversable (Baz t b) where
  traverse f bz = fmap (\m -> Baz (runBazaar m)) . getCompose . runBaz bz $ \x -> Compose $ sell <$> f x

instance Profunctor (Baz t) where
  dimap f g m = Baz $ \k -> runBaz m (fmap f . k . g)

-- | Note: Definitions in terms of 'wander' are much more efficient!
class (Choice p, Strong p) => Traversing p where
  -- | Laws:
  --
  -- @
  -- 'traverse'' ≡ 'wander' 'traverse'
  -- 'traverse'' '.' 'rmap' f ≡ 'rmap' ('fmap' f) '.' 'traverse''
  -- 'traverse'' '.' 'traverse'' ≡ 'dimap' 'Compose' 'getCompose' '.' 'traverse''
  -- 'dimap' 'Identity' 'runIdentity' '.' 'traverse'' ≡ 'id'
  -- @
  traverse' :: Traversable f => p a b -> p (f a) (f b)
  traverse' = wander traverse

  -- | This combinator is mutually defined in terms of 'traverse''
  wander :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> p a b -> p s t
  wander f pab = dimap (\s -> Baz $ \afb -> f afb s) sold (traverse' pab)

  {-# MINIMAL wander | traverse' #-}

instance Traversing (->) where
  traverse' = fmap
  wander f ab = runIdentity #. f (Identity #. ab)

instance Monoid m => Traversing (Forget m) where
  traverse' (Forget h) = Forget (foldMap h)
  wander f (Forget h) = Forget (getConst . f (Const . h))

instance Monad m => Traversing (Kleisli m) where
  traverse' (Kleisli m) = Kleisli (mapM m)
  wander f (Kleisli amb) = Kleisli $ unwrapMonad #. f (WrapMonad #. amb)

instance Applicative m => Traversing (Star m) where
  traverse' (Star m) = Star (traverse m)
  wander f (Star amb) = Star (f amb)

instance (Functor f, Traversing p) => Traversing (Tannen f p) where
  traverse' = Tannen . fmap traverse' . runTannen

newtype CofreeTraversing p a b = CofreeTraversing { runCofreeTraversing :: forall f. Traversable f => p (f a) (f b) }

instance Profunctor p => Profunctor (CofreeTraversing p) where
  lmap f (CofreeTraversing p) = CofreeTraversing (lmap (fmap f) p)
  rmap g (CofreeTraversing p) = CofreeTraversing (rmap (fmap g) p)
  dimap f g (CofreeTraversing p) = CofreeTraversing (dimap (fmap f) (fmap g) p)

instance Profunctor p => Strong (CofreeTraversing p) where
  second' = traverse'

instance Profunctor p => Choice (CofreeTraversing p) where
  right' = traverse'

instance Profunctor p => Traversing (CofreeTraversing p) where
  -- !@(#*&() Compose isn't representational in its second arg or we could use #. and .#
  traverse' (CofreeTraversing p) = CofreeTraversing (dimap Compose getCompose p)

instance ProfunctorFunctor CofreeTraversing where
  promap f (CofreeTraversing p) = CofreeTraversing (f p)

instance ProfunctorComonad CofreeTraversing where
  proextract (CofreeTraversing p) = runIdentity #. p .# Identity
  produplicate (CofreeTraversing p) = CofreeTraversing (CofreeTraversing (dimap Compose getCompose p))

-- | @FreeTraversing -| CofreeTraversing@
data FreeTraversing p a b where
  FreeTraversing :: Traversable f => (f y -> b) -> p x y -> (a -> f x) -> FreeTraversing p a b

instance Profunctor (FreeTraversing p) where
  lmap f (FreeTraversing l m r) = FreeTraversing l m (r . f)
  rmap g (FreeTraversing l m r) = FreeTraversing (g . l) m r
  dimap f g (FreeTraversing l m r) = FreeTraversing (g . l) m (r . f)
  g #. FreeTraversing l m r = FreeTraversing (g #. l) m r
  FreeTraversing l m r .# f = FreeTraversing l m (r .# f)

instance Strong (FreeTraversing p) where
  second' = traverse'

instance Choice (FreeTraversing p) where
  right' = traverse'

instance Traversing (FreeTraversing p) where
  traverse' (FreeTraversing l m r) = FreeTraversing (fmap l .# getCompose) m (Compose #. fmap r)

instance ProfunctorFunctor FreeTraversing where
  promap f (FreeTraversing l m r) = FreeTraversing l (f m) r

instance ProfunctorMonad FreeTraversing where
  proreturn p = FreeTraversing runIdentity p Identity
  projoin (FreeTraversing l (FreeTraversing l' m r') r) = FreeTraversing ((l . fmap l') .# getCompose) m (Compose #. (fmap r' . r))
