{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE ViewPatterns #-}

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

import Control.Arrow (Arrow(..), Kleisli(..))
import Control.Comonad (Cokleisli(..))
#if !MIN_VERSION_base(4,18,0)
import Control.Applicative (Applicative(liftA2))
#endif
import Data.Bifunctor.Joker
import Data.Bifunctor.Clown
import Data.Bifunctor.Biff
import Data.Bifunctor.Tannen
import Data.Functor.Contravariant.Divisible
import Data.Profunctor.Cayley
import Data.Profunctor.Types
import Data.Profunctor.Unsafe
import Data.Tagged

class Profunctor p => Monoidal p where
  {-# minimal pappend, (pempty | ppure) #-}
  pempty :: p () ()
  pappend :: p a b -> p c d -> p (a, c) (b, d)

  -- the unit of day convolution is 'Tagged', which is isomorphic to just the second element
  ppure :: b -> p a b
  pappendWith :: (e -> (a, c)) -> (b -> d -> f) -> p a b -> p c d -> p e f

  ppure = \b -> dimap (const ()) (const b) pempty
  pempty = ppure ()
  pappendWith f g p q = dimap f (uncurry g) $ pappend p q
  pappend = pappendWith id (,)
  {-# inline pempty #-}
  {-# inline ppure #-}
  {-# inline pappend #-}
  {-# inline pappendWith #-}

instance Monoidal Tagged where
  ppure = Tagged
  pempty = Tagged ()
  pappend = \(Tagged a) (Tagged b) -> Tagged (a, b)
  pappendWith = \_ f (Tagged a) (Tagged b) -> Tagged (f a b)
  {-# inline pempty #-}
  {-# inline ppure #-}
  {-# inline pappend #-}
  {-# inline pappendWith #-}

instance Monoid r => Monoidal (Forget r) where
  ppure _ = Forget mempty
  pempty = Forget mempty
  pappend = \(Forget f) (Forget g) ->
    Forget \(a,b) -> f a <> g b
  pappendWith = \f _ (Forget g) (Forget h) ->
    Forget \e -> case f e of
      (a, c) -> g a <> h c
  {-# inline pempty #-}
  {-# inline ppure #-}
  {-# inline pappend #-}
  {-# inline pappendWith #-}

instance Applicative f => Monoidal (Star f) where
  ppure = Star . pure . pure
  pempty = Star pure
  pappend = \(Star f) (Star g) ->
    Star \(a,c) -> liftA2 (,) (f a) (g c)
  pappendWith = \f g (Star h) (Star i) ->
    Star \(f -> (h -> fb, i -> fd)) -> liftA2 g fb fd
  {-# inline pempty #-}
  {-# inline ppure #-}
  {-# inline pappend #-}
  {-# inline pappendWith #-}

instance Functor f => Monoidal (Costar f) where
  ppure = \a -> Costar \_ -> a
  pempty = Costar \_ -> ()
  pappend = \(Costar f) (Costar g) ->
    Costar $ \fp -> (f (fst <$> fp), g (snd <$> fp))
  pappendWith = \f g (Costar h) (Costar i) ->
    Costar $ uncurry g . (h . fmap fst &&& i . fmap snd) . fmap f
  {-# inline pempty #-}
  {-# inline ppure #-}
  {-# inline pappend #-}
  {-# inline pappendWith #-}

instance Applicative f => Monoidal (Kleisli f) where
  ppure = Kleisli . pure . pure
  pempty = Kleisli pure
  pappend = \(Kleisli f) (Kleisli g) ->
    Kleisli \(a,c) -> liftA2 (,) (f a) (g c)
  pappendWith = \f g (Kleisli h) (Kleisli i) ->
    Kleisli \(f -> (h -> fb, i -> fd)) -> liftA2 g fb fd
  {-# inline pempty #-}
  {-# inline ppure #-}
  {-# inline pappend #-}
  {-# inline pappendWith #-}

instance Functor f => Monoidal (Cokleisli f) where
  ppure = \a -> Cokleisli \_ -> a
  pempty = Cokleisli \_ -> ()
  pappend = \(Cokleisli f) (Cokleisli g) ->
    Cokleisli \fp -> (f (fst <$> fp), g (snd <$> fp))
  pappendWith = \f g (Cokleisli h) (Cokleisli i) ->
    Cokleisli $ uncurry g . (h . fmap fst &&& i . fmap snd) . fmap f
      -- \(fmap f -> fac) -> g (h $ fst <$> fac) (i $ snd <$> fac)
  {-# inline pempty #-}
  {-# inline ppure #-}
  {-# inline pappend #-}
  {-# inline pappendWith #-}

instance Applicative f => Monoidal (Joker f) where
  ppure = Joker #. pure
  pempty = Joker $ pure ()
  pappend (Joker f) (Joker g) = Joker $ liftA2 (,) f g
  pappendWith _ f (Joker g) (Joker h) = Joker $ liftA2 f g h
  {-# inline ppure #-}
  {-# inline pempty #-}
  {-# inline pappend #-}
  {-# inline pappendWith #-}

instance Divisible f => Monoidal (Clown f) where
  ppure = \_ -> Clown conquer
  pempty = Clown conquer
  pappend (Clown f) (Clown g) = Clown (divided f g)
  pappendWith f _ (Clown g) (Clown h) = Clown (divide f g h)
  {-# inline ppure #-}
  {-# inline pempty #-}
  {-# inline pappend #-}
  {-# inline pappendWith #-}

instance Arrow p => Monoidal (WrappedArrow p) where
  pempty = arr \_ -> ()
  ppure a = arr \_ -> a
  pappend = (***)
  pappendWith f g h i = dimap f (uncurry g) (h *** i)
  {-# inline pempty #-}
  {-# inline ppure #-}
  {-# inline pappend #-}
  {-# inline pappendWith #-}

instance (Applicative f, Monoidal p) => Monoidal (Tannen f p) where
  ppure = Tannen #. pure . ppure
  pempty = Tannen $ pure pempty
  pappend = \(Tannen f) (Tannen g) ->
    Tannen $ liftA2 pappend f g
  pappendWith = \f g (Tannen h) (Tannen i) ->
    Tannen $ liftA2 (pappendWith f g) h i
  {-# inline pempty #-}
  {-# inline ppure #-}
  {-# inline pappend #-}
  {-# inline pappendWith #-}

instance (Applicative f, Monoidal p) => Monoidal (Cayley f p) where
  ppure = Cayley #. pure . ppure
  pempty = Cayley $ pure pempty
  pappend = \(Cayley f) (Cayley g) -> Cayley (liftA2 pappend f g)
  pappendWith = \f g (Cayley h) (Cayley i) ->
    Cayley $ liftA2 (pappendWith f g) h i
  {-# inline pempty #-}
  {-# inline ppure #-}
  {-# inline pappend #-}
  {-# inline pappendWith #-}

instance (Monoidal p, Functor f, Applicative g) => Monoidal (Biff p f g) where
  ppure = Biff . ppure . pure
  pempty = Biff $ ppure $ pure ()
  pappend (Biff f) (Biff g) = Biff $ pappendWith
    (fmap fst &&& fmap snd) (liftA2 (,)) f g
  pappendWith h i (Biff f) (Biff g) = Biff $ pappendWith
    ((fmap fst &&& fmap snd) . fmap h) (liftA2 i) f g
  {-# inline ppure #-}
  {-# inline pempty #-}
  {-# inline pappend #-}
  {-# inline pappendWith #-}
