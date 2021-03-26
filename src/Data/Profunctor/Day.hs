{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
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
, monday
, oneday
) where

import Data.Profunctor
import Data.Profunctor.Monoidal
import Data.Profunctor.Unsafe
import Data.Tagged

-- 'Tagged' is the unit of @profunctor@ 'Day' convolution
data Day p q s t where
  Day 
    :: (s -> (a, c)) 
    -> ((b, d) -> t)
    -> p a b
    -> q c d
    -> Day p q s t

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

monday :: Monoidal p => Day p p :-> p
monday = \(Day g f p q) -> dimap g f $ pappend p q
{-# inline monday #-}

oneday :: Monoidal p => Tagged :-> p
oneday = ppure .# unTagged
{-# inline oneday #-}
