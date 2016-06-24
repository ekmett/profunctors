{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Profunctor.Traversing
  ( Traversing(..)
  , CofreeTraversing(..)
  , FreeTraversing(..)
  -- * Strong in terms of Traversing
  , firstTraversing
  , secondTraversing
  -- * Choice in terms of Traversing
  , leftTraversing
  , rightTraversing
  -- * Traversing an ArrowChoice
  , wanderA
  , traverseA
  ) where

import Prelude hiding (id, (.))
import Control.Category
import Control.Applicative hiding (WrappedArrow(..))
import Control.Arrow
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Orphans ()
import Data.Profunctor.Choice
import Data.Profunctor.Monad
import Data.Profunctor.Strong
import Data.Profunctor.Types
import Data.Profunctor.Unsafe
import Data.Traversable

#if __GLASGOW_HASKELL__ < 710
import Data.Monoid (Monoid)
import Data.Foldable
import Prelude hiding (mapM)
#endif

firstTraversing :: Traversing p => p a b -> p (a, c) (b, c)
firstTraversing = wander (\f (a, b) -> (\a' -> (a', b)) <$> f a)

secondTraversing :: Traversing p => p a b -> p (c, a) (c, b)
secondTraversing = traverse'

leftTraversing :: Traversing p => p a b -> p (Either a c) (Either b c)
leftTraversing = wander (\f -> either (fmap Left . f) (pure . Right))

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

infixl 4 :<*>

-- A list of values that have been traversed over so far. d is the input type;
-- e is the planned output.
data TList d e a where
  TNil :: TList d e ()
  (:<*>) :: d -> TList d e u -> TList d e (e, u)

-- Trav is a Church-encoded free applicative, which is used to make traversing
-- and assembling a TList faster by left-associating and bringing all the
-- fmaps to the top. See https://www.eyrie.org/~zednenem/2013/06/freeapp-2 for
-- details.
newtype Trav d e a = Trav (forall u y z. (forall x. (x -> y) -> TList d e x -> z) -> (u -> a -> y) -> TList d e u -> z)

instance Functor (Trav d e) where
  {-# INLINE fmap #-}
  fmap f (Trav m) = Trav $ \k s -> m k (\u -> s u . f)

  {-# INLINE (<$) #-}
  a <$ Trav m = Trav $ \k s -> m k (\u -> const $ s u a)

instance Applicative (Trav d e) where
  {-# INLINE pure #-}
  pure a = Trav $ \k s -> k (flip s a)

  {-# INLINE (<*>) #-}
  Trav mf <*> Trav ma = Trav $ \k s -> ma (mf k) (\u a g -> s u (g a))

-- Coyoneda encoding of a Functor.
data Coyo f a where
  Coyo :: (u -> a) -> f u -> Coyo f a

-- Lift a d into an appropriate Trav with an unknown return type.
{-# INLINE tLift #-}
tLift :: d -> Trav d e e
tLift d = Trav $ \k s p -> k (\ (a, u) -> s u a) (d :<*> p)

-- Convert the Trav into an actual list.
{-# INLINE runTrav #-}
runTrav :: Trav d e a -> Coyo (TList d e) a
runTrav (Trav m) = m Coyo (const id) TNil

-- Split a Coyoneda-encoded TList into something an ArrowChoice can traverse.
{-# INLINE unTList #-}
unTList :: Coyo (TList d e) a -> Either a (d, Coyo (TList d e) (e -> a))
unTList (Coyo f TNil) = Left (f ())
unTList (Coyo f (d :<*> t)) = Right (d, Coyo (\u e -> f (e, u)) t)

{-# INLINE wanderA #-}
wanderA :: forall p a b s t. (ArrowChoice p)
  => (forall f. (Applicative f) => (a -> f b) -> s -> f t)
  -> p a b -> p s t
wanderA tr p = go . arr (runTrav . tr tLift) where
  go :: forall u. p (Coyo (TList a b) u) u
  go = (id ||| arr (uncurry $ flip id) . (p *** go)) . arr unTList

{-# INLINE traverseA #-}
traverseA :: (ArrowChoice p, Traversable f) => p a b -> p (f a) (f b)
traverseA = wanderA traverse

-- | Note: Definitions in terms of 'wander' are much more efficient!
class (Choice p, Strong p) => Traversing p where
  traverse' :: Traversable f => p a b -> p (f a) (f b)
  traverse' = wander traverse

  wander :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> p a b -> p s t
  wander f pab = dimap (\s -> Baz $ \afb -> f afb s) sold (traverse' pab)

#if __GLASGOW_HASKELL__ >= 706
  {-# MINIMAL wander | traverse' #-}
#endif

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

instance ArrowChoice p => Traversing (WrappedArrow p) where
  wander f (WrapArrow p) = WrapArrow $ wanderA f p

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
