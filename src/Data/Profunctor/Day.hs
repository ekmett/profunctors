{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ViewPatterns #-}

-- |
-- Copyright   : (C) 2012-2021 Edward Kmett,
-- License     : BSD-2-Clause
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : portable
--
-- Day convolution for profunctors

module Data.Profunctor.Day
( Day(..)
, assoc, unassoc
, lambda, unlambda
, rho, unrho
, swapped
, trans1
, trans2
, monday
, oneday
) where

import Data.Coerce
import Data.Profunctor
import Data.Profunctor.Functor
import Data.Profunctor.Monad
import Data.Profunctor.Monoidal
import Data.Profunctor.Unsafe
import Data.Tagged
import Data.Tuple

-- 'Tagged' is the unit of @profunctor@ 'Day' convolution
type role Day representational representational representational representational
data Day p q s t where
  Day
    :: (s -> (a, c))
    -> ((b, d) -> t)
    -> p a b
    -> q c d
    -> Day p q s t

instance Functor (Day p q s) where
  fmap = \h (Day f g p q) -> Day f (h . g) p q
  {-# inline fmap #-}

instance (Profunctor p, Profunctor q) => Profunctor (Day p q) where
  dimap = \f g (Day f' g' p q) -> Day (f' . f) (g . g') p q
  lmap = \f (Day f' g p q) -> Day (f' . f) g p q
  rmap = \g (Day f g' p q) -> Day f (g . g') p q
  (#.) = \_ -> coerce
  (.#) = \p _ -> coerce p
  {-# inline dimap #-}
  {-# inline lmap #-}
  {-# inline rmap #-}
  {-# inline (#.) #-}
  {-# inline (.#) #-}

-- (p :-> q) -> Day r p :-> Day r q
instance Profunctor p => ProfunctorFunctor (Day p) where
  promap = \h (Day f g p q) -> Day f g p (h q)
  {-# inline promap #-}

-- p :-> Day r p
-- Day r (Day r p) :-> Day r p
instance Monoidal p => ProfunctorMonad (Day p) where
  proreturn = Day ((),) snd pempty
  {-# inline proreturn #-}

  projoin = \(Day f g p (Day h i p' q)) ->
    Day
      (\(f -> (a1,h -> (a2,c1))) -> ((a1,a2),c1))
      (\((b1,b2),d1) -> g (b1, i (b2,d1)))
      (pappend p p')
      q
  {-# inline projoin #-}

assoc :: Day (Day p q) r :-> Day p (Day q r)
assoc = \(Day i h (Day g f p q) r) -> Day
  (\(i -> (g -> (a1,c1), c)) -> (a1, (c1, c)))
  (\(b1,(d1,d)) -> h (f (b1,d1), d))
  p
  (Day id id q r)
{-# inline assoc #-}

unassoc :: Day p (Day q r) :-> Day (Day p q) r
unassoc = \(Day i h p (Day g f q r)) ->
  Day
    (\(i -> (a, g -> (a1,c1))) -> ((a,a1),c1))
    (\((b,b1),d1) -> h (b, f (b1,d1)))
    (Day id id p q)
    r
{-# inline unassoc #-}

lambda :: p :-> Day Tagged p
lambda = Day ((),) snd (Tagged ())
{-# inline lambda #-}

unlambda :: Profunctor p => Day Tagged p :-> p
unlambda = \(Day g f (Tagged x) p) -> dimap (snd . g) (f . (x,)) p
{-# inline unlambda #-}

rho :: p :-> Day p Tagged
rho = \p -> Day (,()) fst p (Tagged ())
{-# inline rho #-}

unrho :: Profunctor p => Day p Tagged :-> p
unrho = \(Day g f p (Tagged x)) -> dimap (fst . g) (f . (,x)) p
{-# inline unrho #-}

-- | Apply a profunctor homomorphism to the left-hand side of a Day convolution.
trans1 :: (p :-> q) -> Day p r :-> Day q r
trans1 = \f (Day h i j k) -> Day h i (f j) k
{-# inline trans1 #-}

-- | Apply a profunctor homomorphism to the left-hand side of a Day convolution.
trans2 :: (p :-> q) -> Day r p :-> Day r q
trans2 = \f (Day h i j k) -> Day h i j (f k)
{-# inline trans2 #-}

swapped :: Day p q :-> Day q p
swapped (Day f g p q) = Day (swap . f) (g . swap) q p
{-# inline swapped #-}

monday :: Monoidal p => Day p p :-> p
monday = \(Day g f p q) -> pappendWith g (curry f) p q
{-# inline monday #-}

oneday :: Monoidal p => Tagged :-> p
oneday = ppure .# unTagged
{-# inline oneday #-}
