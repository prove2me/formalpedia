-- Prove2me | Theorems.Thm_HalfPlane_card_lowAxis
-- name    : HalfPlane.card_lowAxis
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:35:19.654568+00:00
-- url     : https://prove2.me/theorems/ff1bd775-3ad2-4682-8398-212cf00447c5
-- title:
--   The axis part of the low half-plane consists of the two families `(0,u)` and `(u,0)`
-- statement:
--   The axis part of the low half-plane consists of the two families `(0,u)` and `(u,0)`
--   with `u` a square root of `1` below `N/2`.
--
--   ```lean
--   theorem HalfPlane.card_lowAxis(N : ℕ) (hN : 2 ≤ N) :
--       (lowAxis N).card = 2 * unitRootCount N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/HalfPlaneReflection.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/HalfPlaneReflection.lean#L135

-- Thm stub generated from MachineLearning/HalfPlaneReflection.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCRTSeparable
import Definitions.Def_MachineLearning_HalfPlaneCircleBasic
import Definitions.Def_MachineLearning_HalfPlaneReflection

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

open HalfPlane

open Finset

/-! ### The low, high, inner and axis parts of the circle -/











/-! ### Reflecting one coordinate preserves the circle -/



/-! ### The antipodal bijection between the inner low set and the high corner -/



/-! ### The axis part -/

theorem HalfPlane.card_lowAxis(N : ℕ) (hN : 2 ≤ N) :
    (lowAxis N).card = 2 * unitRootCount N := by sorry
