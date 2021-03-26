{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE Safe #-}

-- |
-- Copyright   :  (C) 2012-2021 Edward Kmett,
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
-- Monoidal profunctors

module Data.Profunctor.Monoidal
( Monoidal(..)
) where

import Control.Arrow (Kleisli(..))
import Control.Comonad (Cokleisli(..))
import Control.Applicative
import Data.Profunctor
import Data.Tagged

class Profunctor p => Monoidal p where
  {-# minimal pappend, (pempty | ppure) #-}
  pempty :: p () ()
  pappend :: p a b -> p c d -> p (a, c) (b, d)

  ppure :: b -> p a b
  ppure b = dimap (const ()) (const b) pempty

  pempty = ppure ()
  {-# inline pempty #-}
  {-# inline ppure #-}

instance Monoidal Tagged where
  ppure = Tagged
  pempty = Tagged ()
  pappend (Tagged a) (Tagged b) = Tagged (a, b)
  {-# inline pempty #-}
  {-# inline ppure #-}
  {-# inline pappend #-}

instance Monoid r => Monoidal (Forget r) where
  ppure _ = Forget mempty
  pempty = Forget mempty
  pappend (Forget f) (Forget g) = Forget \(a,b) -> f a <> g b
  {-# inline pempty #-}
  {-# inline ppure #-}
  {-# inline pappend #-}

instance Applicative f => Monoidal (Star f) where
  ppure = Star . pure . pure
  pempty = Star pure
  pappend = \(Star f) (Star g) ->
    Star \(a,c) -> liftA2 (,) (f a) (g c)
  {-# inline pempty #-}
  {-# inline ppure #-}
  {-# inline pappend #-}

instance Functor f => Monoidal (Costar f) where
  ppure = \a -> Costar \_ -> a
  pempty = Costar \_ -> ()
  pappend = \(Costar f) (Costar g) ->
    Costar $ \fp -> (f (fst <$> fp), g (snd <$> fp))
  {-# inline pempty #-}
  {-# inline ppure #-}
  {-# inline pappend #-}

instance Applicative f => Monoidal (Kleisli f) where
  ppure = Kleisli . pure . pure
  pempty = Kleisli pure
  pappend = \(Kleisli f) (Kleisli g) ->
    Kleisli \(a,c) -> liftA2 (,) (f a) (g c)
  {-# inline pempty #-}
  {-# inline ppure #-}
  {-# inline pappend #-}

instance Functor f => Monoidal (Cokleisli f) where
  ppure = \a -> Cokleisli \_ -> a
  pempty = Cokleisli \_ -> ()
  pappend = \(Cokleisli f) (Cokleisli g) ->
    Cokleisli $ \fp -> (f (fst <$> fp), g (snd <$> fp))
  {-# inline pempty #-}
  {-# inline ppure #-}
  {-# inline pappend #-}
