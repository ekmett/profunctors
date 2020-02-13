{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2015-2018 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  portable
--
----------------------------------------------------------------------------
module Data.Profunctor.Mapping
  ( Mapping(..)
  , CofreeMapping(..)
  , FreeMapping(..)
  -- * Traversing in terms of Mapping
  , wanderMapping
  -- * Closed in terms of Mapping
  , traverseMapping
  , closedMapping
  ) where

import Control.Arrow (Kleisli(..))
import Data.Bifunctor.Tannen
import Data.Distributive
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Profunctor.Choice
import Data.Profunctor.Closed
import Data.Profunctor.Monad
import Data.Profunctor.Strong
import Data.Profunctor.Traversing
import Data.Profunctor.Types
import Data.Profunctor.Unsafe
#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif

class (Traversing p, Closed p) => Mapping p where
  -- | Laws:
  --
  -- @
  -- 'map'' '.' 'rmap' f ≡ 'rmap' ('fmap' f) '.' 'map''
  -- 'map'' '.' 'map'' ≡ 'dimap' 'Data.Functor.Compose.Compose' 'Data.Functor.Compose.getCompose' '.' 'map''
  -- 'dimap' 'Data.Functor.Identity.Identity' 'Data.Functor.Identity.runIdentity' '.' 'map'' ≡ 'id'
  -- @
  map' :: Functor f => p a b -> p (f a) (f b)
  map' = roam fmap

  roam :: ((a -> b) -> s -> t)
       -> p a b -> p s t
  roam f = dimap (\s -> Bar $ \ab -> f ab s) lent . map'

newtype Bar t b a = Bar
  { runBar :: (a -> b) -> t }
  deriving Functor

lent :: Bar t a a -> t
lent m = runBar m id

instance Mapping (->) where
  map' = fmap
  roam f = f

instance (Monad m, Distributive m) => Mapping (Kleisli m) where
  map' (Kleisli f) = Kleisli (collect f)
#if __GLASGOW_HASKELL__ >= 710
  roam f = Kleisli #. genMap f .# runKleisli
#else
  -- We could actually use this implementation everywhere, but it's kind of a
  -- warty mess, and there have been rumblings of WrappedMonad deprecation.
  -- If/when GHC 7.8 moves out of the support window, this will vanish in a
  -- puff of cleanup.
  roam f = (Kleisli . (unwrapMonad .)) #. genMapW f .# ((WrapMonad .) . runKleisli)
    where
      genMapW
        :: (Monad m, Distributive m)
        => ((a -> b) -> s -> t)
        -> (a -> WrappedMonad m b) -> s -> WrappedMonad m t
      genMapW abst amb s = WrapMonad $ (\ab -> abst ab s) <$> distribute (unwrapMonad #. amb)
#endif

genMap :: Distributive f => ((a -> b) -> s -> t) -> (a -> f b) -> s -> f t
genMap abst afb s = fmap (\ab -> abst ab s) (distribute afb)

-- see <https://github.com/ekmett/distributive/issues/12>
instance (Applicative m, Distributive m) => Mapping (Star m) where
  map' (Star f) = Star (collect f)
  roam f = Star #. genMap f .# runStar

instance (Functor f, Mapping p) => Mapping (Tannen f p) where
  map' = Tannen . fmap map' . runTannen

wanderMapping :: Mapping p => (forall f. Applicative f => (a -> f b) -> s -> f t) -> p a b -> p s t
wanderMapping f = roam ((runIdentity .) #. f .# (Identity .))

traverseMapping :: (Mapping p, Functor f) => p a b -> p (f a) (f b)
traverseMapping = map'

closedMapping :: Mapping p => p a b -> p (x -> a) (x -> b)
closedMapping = map'

newtype CofreeMapping p a b = CofreeMapping { runCofreeMapping :: forall f. Functor f => p (f a) (f b) }

instance Profunctor p => Profunctor (CofreeMapping p) where
  lmap f (CofreeMapping p) = CofreeMapping (lmap (fmap f) p)
  rmap g (CofreeMapping p) = CofreeMapping (rmap (fmap g) p)
  dimap f g (CofreeMapping p) = CofreeMapping (dimap (fmap f) (fmap g) p)

instance Profunctor p => Strong (CofreeMapping p) where
  second' = map'

instance Profunctor p => Choice (CofreeMapping p) where
  right' = map'

instance Profunctor p => Closed (CofreeMapping p) where
  closed = map'

instance Profunctor p => Traversing (CofreeMapping p) where
  traverse' = map'
  wander f = roam $ (runIdentity .) #. f .# (Identity .)

instance Profunctor p => Mapping (CofreeMapping p) where
  -- !@(#*&() Compose isn't representational in its second arg or we could use #. and .#
  map' (CofreeMapping p) = CofreeMapping (dimap Compose getCompose p)
  roam f (CofreeMapping p) =
     CofreeMapping $
       dimap (Compose #. fmap (\s -> Bar $ \ab -> f ab s)) (fmap lent .# getCompose) p

instance ProfunctorFunctor CofreeMapping where
  promap f (CofreeMapping p) = CofreeMapping (f p)

instance ProfunctorComonad CofreeMapping where
  proextract (CofreeMapping p) = runIdentity #. p .# Identity
  produplicate (CofreeMapping p) = CofreeMapping (CofreeMapping (dimap Compose getCompose p))

-- | @FreeMapping -| CofreeMapping@
data FreeMapping p a b where
  FreeMapping :: Functor f => (f y -> b) -> p x y -> (a -> f x) -> FreeMapping p a b

instance Profunctor (FreeMapping p) where
  lmap f (FreeMapping l m r) = FreeMapping l m (r . f)
  rmap g (FreeMapping l m r) = FreeMapping (g . l) m r
  dimap f g (FreeMapping l m r) = FreeMapping (g . l) m (r . f)
  g #. FreeMapping l m r = FreeMapping (g #. l) m r
  FreeMapping l m r .# f = FreeMapping l m (r .# f)

instance Strong (FreeMapping p) where
  second' = map'

instance Choice (FreeMapping p) where
  right' = map'

instance Closed (FreeMapping p) where
  closed = map'

instance Traversing (FreeMapping p) where
  traverse' = map'
  wander f = roam ((runIdentity .) #. f .# (Identity .))

instance Mapping (FreeMapping p) where
  map' (FreeMapping l m r) = FreeMapping (fmap l .# getCompose) m (Compose #. fmap r)

instance ProfunctorFunctor FreeMapping where
  promap f (FreeMapping l m r) = FreeMapping l (f m) r

instance ProfunctorMonad FreeMapping where
  proreturn p = FreeMapping runIdentity p Identity
  projoin (FreeMapping l (FreeMapping l' m r') r) = FreeMapping ((l . fmap l') .# getCompose) m (Compose #. (fmap r' . r))
