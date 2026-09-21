{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE Safe #-}
module Main (main) where

import Control.Category
import Control.Monad (forM_, unless)
import Data.Profunctor
import Data.Profunctor.Adjunction
import Data.Profunctor.Composition (Procompose(..))
import qualified Data.Profunctor.Composition as Composition
import Data.Profunctor.Monad
import Data.Profunctor.Rift
import Prelude hiding (id, (.))

assertEqual :: (Eq a, Show a) => String -> a -> a -> IO ()
assertEqual label expected actual = unless (expected == actual) $
  error (label ++ ": expected " ++ show expected ++ ", got " ++ show actual)

composeStar :: Procompose (->) (Star []) :-> Star []
composeStar (Procompose f (Star g)) = Star (map f . g)

liftStar :: Star [] :-> Rift (->) (Star [])
liftStar q = Rift $ \p -> rmap p q

liftFunction :: (a -> b) -> Rift (->) (->) a b
liftFunction f = Rift (. f)

-- Three distinct, non-Type kinds ensure currying and evaluation retain the
-- generality of Procompose and Rift, without requiring Profunctor instances.
newtype P (a :: Bool) (b :: Ordering) = P Int
newtype Q (a :: Maybe Bool) (b :: Bool) = Q Int
newtype R (a :: Maybe Bool) (b :: Ordering) = R Int

composeKinds :: Procompose P Q :-> R
composeKinds (Procompose (P p) (Q q)) = R (10 * p + q)

main :: IO ()
main = do
  forM_ [-3 .. 3 :: Int] $ \x ->
    forM_ [(+ 1), (* 2), negate] $ \f ->
      forM_ [(subtract 3), (* 5)] $ \g -> do
        let q = Star (\a -> [a, a + 2])
            composed = Procompose f q
            r = liftFunction f
            s = liftFunction g
            observe t = runRift t id x
        assertEqual "uncurry/curry" (runStar (composeStar composed) x)
          (runStar (uncurryRift (curryRift composeStar) composed) x)
        assertEqual "curry/uncurry" (runStar (runRift (liftStar q) f) x)
          (runStar (runRift (curryRift (uncurryRift liftStar) q) f) x)
        assertEqual "curry evaluation" (runStar (runRift (liftStar q) f) x)
          (runStar (runRift (curryRift decomposeRift (liftStar q)) f) x)
        assertEqual "uncurry identity" (runStar (decomposeRift (Procompose f (liftStar q))) x)
          (runStar (uncurryRift id (Procompose f (liftStar q))) x)
        assertEqual "postcomposition" (map (g . f) [x, x + 2])
          (runStar (runRift (postcomposeRift (Procompose r q)) g) x)
        assertEqual "profunctor mapping" (g (f (x + 7)))
          (observe (dimap (+ 7) g r))
        assertEqual "functor mapping" (g (f x)) (observe (fmap g r))
        assertEqual "category order" (f (g x)) (observe (r . s))
        assertEqual "left identity" (observe r) (observe (id . r))
        assertEqual "right identity" (observe r) (observe (r . id))
        assertEqual "duplication order" (f (g (x + 1)))
          (runRift (runRift (produplicate (liftFunction (+ 1))) g) f x)
        assertEqual "comonad extract/duplicate" (observe r)
          (observe (proextract (produplicate r)))
        assertEqual "comonad map extract" (observe r)
          (observe (promap proextract (produplicate r)))
        assertEqual "adjunction left triangle" (runStar (composeStar composed) x)
          (runStar (composeStar (counit (promap unit composed))) x)
        assertEqual "adjunction right triangle" (observe r)
          (observe (promap counit (unit r)))
        -- Both import paths must use the same type, constructor and instances.
        assertEqual "legacy export" (observe r)
          (Composition.decomposeRift (Procompose id r) x)
        assertEqual "heterogeneous result" (map show [x, x + 2])
          (runStar (runRift (curryRift composeStar q) show) x)
  let p = P 4 :: P 'True 'LT
      q = Q 2 :: Q ('Just 'False) 'True
      R curried = runRift (curryRift composeKinds q) p
      R uncurried = uncurryRift (curryRift composeKinds) (Procompose p q)
      R evaluated = decomposeRift (Procompose p (curryRift composeKinds q))
  assertEqual "polykinded curry" 42 curried
  assertEqual "polykinded uncurry" 42 uncurried
  assertEqual "polykinded evaluation" 42 evaluated
  putStrLn "Rift laws passed."
