{-# LANGUAGE CPP #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2011-2018 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
-- For a good explanation of profunctors in Haskell see Dan Piponi's article:
--
-- <http://blog.sigfpe.com/2011/07/profunctors-in-haskell.html>
--
-- This module includes /unsafe/ composition operators that are useful in
-- practice when it comes to generating optimal core in GHC.
--
-- If you import this module you are taking upon yourself the obligation
-- that you will only call the operators with @#@ in their names with functions
-- that are operationally identity such as @newtype@ constructors or the field
-- accessor of a @newtype@.
--
-- If you are ever in doubt, use 'rmap' or 'lmap'.
----------------------------------------------------------------------------
module Data.Profunctor.Unsafe
  (
  -- * Profunctors
    Profunctor(..)
  ) where

import Control.Arrow
import Control.Category
import Control.Comonad (Cokleisli(..))
import Control.Monad (liftM)
import Data.Bifunctor.Biff (Biff(..))
import Data.Bifunctor.Clown (Clown(..))
import Data.Bifunctor.Joker (Joker(..))
import Data.Bifunctor.Product (Product(..))
import Data.Bifunctor.Sum (Sum(..))
import Data.Bifunctor.Tannen (Tannen(..))
import Data.Coerce (Coercible, coerce)
#if __GLASGOW_HASKELL__ < 710
import Data.Functor
#endif
import Data.Functor.Contravariant (Contravariant(..))
import Data.Tagged
import Prelude hiding (id,(.))

infixr 9 #.
infixl 8 .#

----------------------------------------------------------------------------
-- Profunctors
----------------------------------------------------------------------------

-- | Formally, the class 'Profunctor' represents a profunctor
-- from @Hask@ -> @Hask@.
--
-- Intuitively it is a bifunctor where the first argument is contravariant
-- and the second argument is covariant.
--
-- You can define a 'Profunctor' by either defining 'dimap' or by defining both
-- 'lmap' and 'rmap'.
--
-- If you supply 'dimap', you should ensure that:
--
-- @'dimap' 'id' 'id' ≡ 'id'@
--
-- If you supply 'lmap' and 'rmap', ensure:
--
-- @
-- 'lmap' 'id' ≡ 'id'
-- 'rmap' 'id' ≡ 'id'
-- @
--
-- If you supply both, you should also ensure:
--
-- @'dimap' f g ≡ 'lmap' f '.' 'rmap' g@
--
-- These ensure by parametricity:
--
-- @
-- 'dimap' (f '.' g) (h '.' i) ≡ 'dimap' g h '.' 'dimap' f i
-- 'lmap' (f '.' g) ≡ 'lmap' g '.' 'lmap' f
-- 'rmap' (f '.' g) ≡ 'rmap' f '.' 'rmap' g
-- @
class Profunctor p where
  -- | Map over both arguments at the same time.
  --
  -- @'dimap' f g ≡ 'lmap' f '.' 'rmap' g@
  dimap :: (a -> b) -> (c -> d) -> p b c -> p a d
  dimap f g = lmap f . rmap g
  {-# INLINE dimap #-}

  -- | Map the first argument contravariantly.
  --
  -- @'lmap' f ≡ 'dimap' f 'id'@
  lmap :: (a -> b) -> p b c -> p a c
  lmap f = dimap f id
  {-# INLINE lmap #-}

  -- | Map the second argument covariantly.
  --
  -- @'rmap' ≡ 'dimap' 'id'@
  rmap :: (b -> c) -> p a b -> p a c
  rmap = dimap id
  {-# INLINE rmap #-}

  -- | Strictly map the second argument argument
  -- covariantly with a function that is assumed
  -- operationally to be a cast, such as a newtype
  -- constructor.
  --
  -- /Note:/ This operation is explicitly /unsafe/
  -- since an implementation may choose to use
  -- 'unsafeCoerce' to implement this combinator
  -- and it has no way to validate that your function
  -- meets the requirements.
  --
  -- If you implement this combinator with
  -- 'unsafeCoerce', then you are taking upon yourself
  -- the obligation that you don't use GADT-like
  -- tricks to distinguish values.
  --
  -- If you import "Data.Profunctor.Unsafe" you are
  -- taking upon yourself the obligation that you
  -- will only call this with a first argument that is
  -- operationally identity.
  --
  -- The semantics of this function with respect to bottoms
  -- should match the default definition:
  --
  -- @('Profuctor.Unsafe.#.') ≡ \\_ -> \\p -> p \`seq\` 'rmap' 'coerce' p@
  (#.) :: forall a b c q. Coercible c b => q b c -> p a b -> p a c
  (#.) = \_ -> \p -> p `seq` rmap (coerce (id :: c -> c) :: b -> c) p
  {-# INLINE (#.) #-}

  -- | Strictly map the first argument argument
  -- contravariantly with a function that is assumed
  -- operationally to be a cast, such as a newtype
  -- constructor.
  --
  -- /Note:/ This operation is explicitly /unsafe/
  -- since an implementation may choose to use
  -- 'unsafeCoerce' to implement this combinator
  -- and it has no way to validate that your function
  -- meets the requirements.
  --
  -- If you implement this combinator with
  -- 'unsafeCoerce', then you are taking upon yourself
  -- the obligation that you don't use GADT-like
  -- tricks to distinguish values.
  --
  -- If you import "Data.Profunctor.Unsafe" you are
  -- taking upon yourself the obligation that you
  -- will only call this with a second argument that is
  -- operationally identity.
  --
  -- @('.#') ≡ \\p -> p \`seq\` \\f -> 'lmap' 'coerce' p@
  (.#) :: forall a b c q. Coercible b a => p b c -> q a b -> p a c
  (.#) = \p -> p `seq` \_ -> lmap (coerce (id :: b -> b) :: a -> b) p
  {-# INLINE (.#) #-}

  {-# MINIMAL dimap | (lmap, rmap) #-}

instance Profunctor (->) where
  dimap ab cd bc = cd . bc . ab
  {-# INLINE dimap #-}
  lmap = flip (.)
  {-# INLINE lmap #-}
  rmap = (.)
  {-# INLINE rmap #-}
  (#.) _ = coerce (\x -> x :: b) :: forall a b. Coercible b a => a -> b
  (.#) pbc _ = coerce pbc
  {-# INLINE (#.) #-}
  {-# INLINE (.#) #-}

instance Profunctor Tagged where
  dimap _ f (Tagged s) = Tagged (f s)
  {-# INLINE dimap #-}
  lmap _ = retag
  {-# INLINE lmap #-}
  rmap = fmap
  {-# INLINE rmap #-}
  (#.) _ = coerce (\x -> x :: b) :: forall a b. Coercible b a => a -> b
  {-# INLINE (#.) #-}
  Tagged s .# _ = Tagged s
  {-# INLINE (.#) #-}

instance Monad m => Profunctor (Kleisli m) where
  dimap f g (Kleisli h) = Kleisli (liftM g . h . f)
  {-# INLINE dimap #-}
  lmap k (Kleisli f) = Kleisli (f . k)
  {-# INLINE lmap #-}
  rmap k (Kleisli f) = Kleisli (liftM k . f)
  {-# INLINE rmap #-}
  -- We cannot safely overload (#.) because we didn't provide the 'Monad'.
  (.#) pbc _ = coerce pbc
  {-# INLINE (.#) #-}

instance Functor w => Profunctor (Cokleisli w) where
  dimap f g (Cokleisli h) = Cokleisli (g . h . fmap f)
  {-# INLINE dimap #-}
  lmap k (Cokleisli f) = Cokleisli (f . fmap k)
  {-# INLINE lmap #-}
  rmap k (Cokleisli f) = Cokleisli (k . f)
  {-# INLINE rmap #-}
  -- We cannot safely overload (.#) because we didn't provide the 'Functor'.
  (#.) _ = coerce (\x -> x :: b) :: forall a b. Coercible b a => a -> b
  {-# INLINE (#.) #-}

instance Contravariant f => Profunctor (Clown f) where
  lmap f (Clown fa) = Clown (contramap f fa)
  {-# INLINE lmap #-}
  rmap _ (Clown fa) = Clown fa
  {-# INLINE rmap #-}
  dimap f _ (Clown fa) = Clown (contramap f fa)
  {-# INLINE dimap #-}

instance Functor f => Profunctor (Joker f) where
  lmap _ (Joker fb) = Joker fb
  {-# INLINE lmap #-}
  rmap g (Joker fb) = Joker (fmap g fb)
  {-# INLINE rmap #-}
  dimap _ g (Joker fb) = Joker (fmap g fb)
  {-# INLINE dimap #-}

instance (Profunctor p, Functor f, Functor g) => Profunctor (Biff p f g) where
  lmap f (Biff p) = Biff (lmap (fmap f) p)
  rmap g (Biff p) = Biff (rmap (fmap g) p)
  dimap f g (Biff p) = Biff (dimap (fmap f) (fmap g) p)

instance (Profunctor p, Profunctor q) => Profunctor (Product p q) where
  lmap  f   (Pair p q) = Pair (lmap f p) (lmap f q)
  {-# INLINE lmap #-}
  rmap    g (Pair p q) = Pair (rmap g p) (rmap g q)
  {-# INLINE rmap #-}
  dimap f g (Pair p q) = Pair (dimap f g p) (dimap f g q)
  {-# INLINE dimap #-}
  (#.) f (Pair p q) = Pair (f #. p) (f #. q)
  {-# INLINE (#.) #-}
  (.#) (Pair p q) f = Pair (p .# f) (q .# f)
  {-# INLINE (.#) #-}

instance (Profunctor p, Profunctor q) => Profunctor (Sum p q) where
  lmap f (L2 x) = L2 (lmap f x)
  lmap f (R2 y) = R2 (lmap f y)
  {-# INLINE lmap #-}
  rmap g (L2 x) = L2 (rmap g x)
  rmap g (R2 y) = R2 (rmap g y)
  {-# INLINE rmap #-}
  dimap f g (L2 x) = L2 (dimap f g x)
  dimap f g (R2 y) = R2 (dimap f g y)
  {-# INLINE dimap #-}
  f #. L2 x = L2 (f #. x)
  f #. R2 y = R2 (f #. y)
  {-# INLINE (#.) #-}
  L2 x .# f = L2 (x .# f)
  R2 y .# f = R2 (y .# f)
  {-# INLINE (.#) #-}

instance (Functor f, Profunctor p) => Profunctor (Tannen f p) where
  lmap f (Tannen h) = Tannen (lmap f <$> h)
  {-# INLINE lmap #-}
  rmap g (Tannen h) = Tannen (rmap g <$> h)
  {-# INLINE rmap #-}
  dimap f g (Tannen h) = Tannen (dimap f g <$> h)
  {-# INLINE dimap #-}
  (#.) f (Tannen h) = Tannen ((f #.) <$> h)
  {-# INLINE (#.) #-}
  (.#) (Tannen h) f = Tannen ((.# f) <$> h)
  {-# INLINE (.#) #-}
