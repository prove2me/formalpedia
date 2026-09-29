-- Prove2me | Theorems.Thm_HalfPlane_four_mul_halfPlaneCount_le
-- name    : HalfPlane.four_mul_halfPlaneCount_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:36:31.784798+00:00
-- url     : https://prove2.me/theorems/e9a7f116-1131-434e-8e81-06300c168079
-- title:
--   The half-plane count is at most a quarter of the circle count, up to the
-- statement:
--   **The half-plane count is at most a quarter of the circle count**, up to the
--   square-root-of-unity correction: `4 H(N) ≤ C(N) + 8 R(N)`.
--
--   ```lean
--   theorem HalfPlane.four_mul_halfPlaneCount_le(N : ℕ) (hN : 2 ≤ N) :
--       4 * halfPlaneCount N ≤ circleCount N + 8 * unitRootCount N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/HalfPlaneReflection.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/HalfPlaneReflection.lean#L319

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


/-! ### The reflection identity -/


/-! ### The quadrant bound -/

theorem HalfPlane.four_mul_halfPlaneCount_le(N : ℕ) (hN : 2 ≤ N) :
    4 * halfPlaneCount N ≤ circleCount N + 8 * unitRootCount N := by sorry
