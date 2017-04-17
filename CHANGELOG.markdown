HEAD
---
* Allow `base-orphans-0.6`.
* Add `pastro` and `unpastro` to `Data.Profunctor.Strong`.
* Add `dimapWandering`, `lmapWandering`, and `rmapWandering` to `Data.Profunctor.Traversing`
* Add documentation stating the laws for various profunctors.
* Introduce the `Data.Profunctor.Yoneda` module.

5.2
---
* Renamed `Cotambara` to `TambaraChoice` and `Pastro` to `PastroChoice`.
* Added a true `Cotambara` and `Copastro` construction for (co)freely generating costrength, along with `CotambaraSum` and `CopastroSum` variants.
* Engaged in a fair bit of bikeshedding about the module structure for lesser used modules in this package.

5.1.2
-----
* Added `Prep` and `Coprep` along with witnesses to the adjunctions `Prep -| Star : [Hask,Hask] -> Prof` and `Coprep -| Costar : [Hask,Hask]^op -> Prof`.

5.1.1
-----
* Add proper support for GHC 7.0+.

5.1
---
* `instance Costrong (Cokleisli f)`.
* `instance Cochoice (Star f)`.
* Changed the instance for `Cochoice (Costar f)`.

5.0.1
-----
* MINIMAL pragma for `Costrong` and `Cochoice`.
* More `Costrong` and `Cochoice` instances.

5.0.0.1
-------
* Documentation fix

5
-
* `UpStar` and `DownStar` have become `Star` and `Costar`. `Star` is analogous to `Kleisli`, `Costar` is analogous to `Cokleisli`.
* Split representability into sieves and representability.
* Moved `Data.Profunctor.Collage` to `semigroupoids` 5, and removed the `semigroupoids` dependency.
* Rather greatly widened the range of GHC versions we can support.

4.4.1
-------
* Using `SafeHaskell`, GHC 7.8+ `Data.Profunctor.Unsafe` now infers as `Trustworthy` and
  many more modules now infer as `Safe`.
* We now build warning-free on GHC 7.10.0.20150307

4.4
-----
* Added `Coercible` constraint to (#.) and (.#) when building with GHC 7.8
* `Strong` is now a superclass of `Representable`
* Updated the URL of the "Arrows are Strong Monads" paper. The old URL is now a dead link.

4.3.2
-----
* Added some missing instances for `UpStar` and `DownStar`.

4.3
---
* Removed the non law-abiding instance for `Closed (Forget r)`
* `Forget` is `Representable`
* MINIMAL pragmas

4.2.0.1
-------
* Avoided using 'type' in the export list, as that doesn't work on 7.4.

4.2
---
* Renamed `-|` to `ProfunctorAdjunction` because GHC 7.4 still exists in the wild.
* Renamed `-/->` to `:->` for the same reason. Also the former was confusing as they conflated profunctor homomorphisms and profunctors themselves.

4.1
---
* Flipped the order of 'Procompose'
* Added the notion of Monads and Comonads on the category of profunctors.
* Added 'Cayley' which takes normal Haskell Monads and Comonads to a 'ProfunctorMonad' and 'ProfunctorComonad' respectively. Cayley is also known as the 'static arrow' construction
* Added 'Closed' which is adjoint to 'Strong'.
* Added 'Closure' which freely adjoins 'Closed' to any 'Profunctor'.
* Added 'Tambara' which freely adjoins 'Strong' to any 'Profunctor'.
* Added 'Cotambara' which freely adjoins 'Choice' to any 'Profunctor'.
* Under the new 'Procompose' the old 'Rift' is now 'Ran', and the old 'Lift' was misnamed. It is now 'Rift'

4.0.3
-----
* Added `Data.Profunctor.Lift` containing the left Kan lift of a profunctor.

4.0.2
-----
* Added `assoc` to `Data.Profunctor.Composition` so that we have all 3 associators.

4.0
---
* Merged the contents of `profunctor-extras` into `profunctors`.

3.3
---
* Added `instance Choice (Upstar f)` and introduced `Forget`.

3.2
---
* Renamed `Lenticular` and `Prismatic` to `Strong` and `Choice`, and restructured them.

3.1.3
-----
* Removed upper bounds on my own intra-package dependencies

3.1.1
-----
* Added Documentation!
* Added `Lenticular` and `Prismatic` Profunctors

3.1
---
* instance Profunctor Tagged

3.0
---
* Updated version number to match the rest of my libraries
