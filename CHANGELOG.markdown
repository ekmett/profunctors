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
