{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE Safe #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Profunctor.Rift
-- Copyright   :  (C) 2026 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  PolyKinds, RankNTypes, TypeOperators
--
-- Right Kan lifts of profunctors. Whereas @t'Data.Profunctor.Ran.Ran' p@
-- is right adjoint to composition on the right by @p@, @'Rift' p@ is
-- right adjoint to composition on the left by @p@:
--
-- @
-- ('Procompose' p q ':->' r) ≅ (q ':->' 'Rift' p r)
-- @
--
-- 'curryRift' and 'uncurryRift' witness this correspondence, and
-- 'decomposeRift' is its evaluation map. For example, with function
-- profunctors, @'curryRift' 'procomposed' f@ is @'Rift' (\\k -> k . f)@.
--
-- The type and its instances are shared with "Data.Profunctor.Composition",
-- which continues to export 'Rift' and 'decomposeRift' for compatibility.
-----------------------------------------------------------------------------
module Data.Profunctor.Rift
  ( Rift(..)
  , decomposeRift
  , postcomposeRift
  , curryRift
  , uncurryRift
  ) where

import Data.Profunctor
import Data.Profunctor.Composition

-- | Compose a right Kan lift into the function profunctor with a
-- profunctor @q@. This is the counterpart of
-- 'Data.Profunctor.Ran.precomposeRan' for right Kan lifts.
--
-- @
-- 'runRift' ('postcomposeRift' ('Procompose' f q)) p = 'rmap' ('runRift' f p) q
-- @
postcomposeRift :: Profunctor q => Procompose (Rift p (->)) q :-> Rift p q
postcomposeRift (Procompose f q) = Rift $ \p -> rmap (runRift f p) q
{-# INLINE postcomposeRift #-}

-- | Transpose a transformation out of a composition into a right Kan lift.
-- No 'Profunctor' constraints are needed, and all three underlying kinds
-- may differ.
--
-- @
-- 'uncurryRift' ('curryRift' f) = f
-- 'curryRift' 'decomposeRift' = id
-- @
curryRift :: (Procompose p q :-> r) -> q :-> Rift p r
curryRift f q = Rift $ \p -> f (Procompose p q)
{-# INLINE curryRift #-}

-- | Evaluate a transformation into a right Kan lift on a composition.
-- This is the inverse of 'curryRift'.
--
-- @
-- 'curryRift' ('uncurryRift' f) = f
-- 'uncurryRift' id = 'decomposeRift'
-- @
uncurryRift :: (q :-> Rift p r) -> Procompose p q :-> r
uncurryRift f (Procompose p q) = runRift (f q) p
{-# INLINE uncurryRift #-}
