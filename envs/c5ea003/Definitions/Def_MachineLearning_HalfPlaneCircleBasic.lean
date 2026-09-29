-- Prove2me | Definitions.Def_MachineLearning_HalfPlaneCircleBasic
-- name    : MachineLearning_HalfPlaneCircleBasic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:40:01.725033+00:00
-- url     : https://prove2.me/theorems/0ecacfb6-2445-4f5b-8acf-52d83d744df4
-- title:
--   Aether Catalog definitions — MachineLearning_HalfPlaneCircleBasic
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.HalfPlaneCircleBasic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/HalfPlaneCircleBasic.lean by skeleton subtraction
import Mathlib

/-!
# The half-plane circle count: basic definitions

For a modulus `N` we study the *modular circle*

  `Circle(N) = {(x, y) ∈ [0,N)² : x² + y² ≡ 1 (mod N)}`

together with the **non-CRT-separable** half-plane cut `x + y < N/2`
(the sum `x + y` is taken as an *integer*, not modulo `N`, which is exactly
what destroys separability).

This file sets up:

* `circleFinset N`  — the circle as a finite set of pairs of naturals,
* `circleCount N`   — its cardinality `C(N)`,
* `halfPlaneCount N`— the count `H(N)` of circle points in the low half-plane
  `2(x+y) < N`,
* `highCount N`     — the count of circle points with `2(x+y) > 3N`,
* `unitRootCount N` — the number of square roots of `1` below `N/2`,

and the bridge to the algebraic description of the circle inside `ZMod N`,
which is what makes the Chinese Remainder analysis possible.
-/

namespace HalfPlane

open Finset

/-- The modular circle `x² + y² ≡ 1 (mod N)` with representatives in `[0,N)`. -/
def circleFinset (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range N ×ˢ Finset.range N).filter (fun p => (p.1 ^ 2 + p.2 ^ 2) % N = 1 % N)

/-- `C(N)`: the number of points of the modular circle. -/
def circleCount (N : ℕ) : ℕ := (circleFinset N).card

/-- `H(N)`: the number of circle points in the half-plane `x + y < N/2`. -/
def halfPlaneCount (N : ℕ) : ℕ :=
  ((circleFinset N).filter (fun p => 2 * (p.1 + p.2) < N)).card

/-- The number of circle points in the *opposite* corner `x + y > 3N/2`. -/
def highCount (N : ℕ) : ℕ :=
  ((circleFinset N).filter (fun p => 3 * N < 2 * (p.1 + p.2))).card

/-- The number of square roots of `1` modulo `N` lying below `N/2`. -/
def unitRootCount (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun u => 2 * u < N ∧ u ^ 2 % N = 1 % N)).card

/-- The circle described inside `ZMod N`. -/
def circleZ (N : ℕ) [NeZero N] : Finset (ZMod N × ZMod N) :=
  Finset.univ.filter (fun q => q.1 ^ 2 + q.2 ^ 2 = 1)

section Basic

variable {N : ℕ}





end Basic

/-! ### Small-case data (Lab Notes)

```
N :  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19 20
C :  1  2  4  8  4  8  8 16 12  8 12 32 12 16 16 32 16 24 20 32
H :  1  0  2  2  2  2  2  4  4  2  2  6  2  2  4  6  3  4  4  6
```
-/

end HalfPlane


