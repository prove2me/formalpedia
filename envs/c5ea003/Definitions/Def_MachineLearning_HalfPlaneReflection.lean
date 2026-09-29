-- Prove2me | Definitions.Def_MachineLearning_HalfPlaneReflection
-- name    : MachineLearning_HalfPlaneReflection
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:41:56.397982+00:00
-- url     : https://prove2.me/theorems/182b3048-2f4a-4f4b-820b-e09d17e4b093
-- title:
--   Aether Catalog definitions — MachineLearning_HalfPlaneReflection
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.HalfPlaneReflection`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/HalfPlaneReflection.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCRTSeparable
import Definitions.Def_MachineLearning_HalfPlaneCircleBasic

/-!
# The half-plane cut: reflection identity, quadrant bound, and non-separability

The cut `x + y < N/2` uses the *integer* sum of the representatives and is therefore
**not** a CRT-separable condition.  Nevertheless the count `H(N)` is rigidly
controlled by the reflection symmetries of the circle:

* `halfPlaneCount_eq_highCount_add` :
  `H(N) = high(N) + 2 · R(N)` for `N ≥ 2`, where `high(N)` counts the circle points
  in the *opposite* corner `x + y > 3N/2` and `R(N)` is the number of square roots
  of `1` below `N/2` (the "axis" points `(0, u)` and `(u, 0)`).
  The bijection is the antipodal map `(x, y) ↦ (N - x, N - y)`.

* `four_mul_highCount_le_circleCount` :
  `4 · high(N) ≤ C(N)`, via four pairwise disjoint copies of the corner
  produced by the reflection group `⟨x ↦ N - x, y ↦ N - y⟩`.

* `four_mul_halfPlaneCount_le` :
  `4 · H(N) ≤ C(N) + 8 · R(N)`, i.e. `H` is at most a quarter of the circle count
  up to the (tiny, `2^ω(N)`-sized) square-root-of-unity correction.

* `halfPlaneCount_not_multiplicative` : `H` is **not** CRT-separable:
  `H(35) = 6 ≠ 4 = H(5) · H(7)`, while `C(35) = C(5) · C(7)`.
  This is the formal statement of the "classification boundary".
-/

namespace HalfPlane

open Finset

/-! ### The low, high, inner and axis parts of the circle -/

/-- Circle points in the low half-plane `2(x+y) < N`. -/
def lowFinset (N : ℕ) : Finset (ℕ × ℕ) :=
  (circleFinset N).filter (fun p => 2 * (p.1 + p.2) < N)

/-- Circle points in the opposite corner `2(x+y) > 3N`. -/
def highFinset (N : ℕ) : Finset (ℕ × ℕ) :=
  (circleFinset N).filter (fun p => 3 * N < 2 * (p.1 + p.2))

/-- Low points off the coordinate axes. -/
def lowInner (N : ℕ) : Finset (ℕ × ℕ) :=
  (lowFinset N).filter (fun p => 1 ≤ p.1 ∧ 1 ≤ p.2)

/-- Low points on a coordinate axis. -/
def lowAxis (N : ℕ) : Finset (ℕ × ℕ) :=
  (lowFinset N).filter (fun p => ¬ (1 ≤ p.1 ∧ 1 ≤ p.2))

/-- Square roots of `1` modulo `N` lying below `N/2`. -/
def unitRootFinset (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun u => 2 * u < N ∧ u ^ 2 % N = 1 % N)






/-! ### Reflecting one coordinate preserves the circle -/



/-! ### The antipodal bijection between the inner low set and the high corner -/



/-! ### The axis part -/


/-! ### The reflection identity -/


/-! ### The quadrant bound -/



/-! ### Non-separability of the half-plane count

The circle count is a product of local factors; the half-plane count is not. -/




/-! ### Lab notes: the reflection identity in action

```
N        : 15  16  17  20  21  24  25  28  33  35
H(N)     :  4   6   3   6   4  12   6  10   8   6
high(N)  :  0   2   1   2   0   4   4   6   4   2
R(N)     :  2   2   1   2   2   4   1   2   2   2
4·high   :  0   8   4   8   0  16  16  24  16   8
C(N)     : 16  32  16  32  32  64  20  64  48  32
```
Each column satisfies `H = high + 2R` and `4·high ≤ C`.
-/

end HalfPlane


