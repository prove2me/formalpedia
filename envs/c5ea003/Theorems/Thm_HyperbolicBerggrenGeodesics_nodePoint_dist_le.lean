-- Prove2me | Theorems.Thm_HyperbolicBerggrenGeodesics_nodePoint_dist_le
-- name    : HyperbolicBerggrenGeodesics.nodePoint_dist_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:27:30.553456+00:00
-- url     : https://prove2.me/theorems/3748fa6d-9699-4dfe-84da-960876ef16b0
-- title:
--   Every node of the box lies within hyperbolic distance `log K + 2` of the base point.
-- statement:
--   Every node of the box lies within hyperbolic distance `log K + 2` of the base point.
--
--   ```lean
--   theorem HyperbolicBerggrenGeodesics.nodePoint_dist_le{K : ℕ} (hK : 256 ≤ K) {p : ℕ × ℕ} (hp : p ∈ seedBox K) :
--       dist (nodePoint p) UpperHalfPlane.I ≤ Real.log K + 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/HyperbolicBerggrenDensity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/HyperbolicBerggrenDensity.lean#L357

-- Thm stub generated from Geometry/HyperbolicBerggrenDensity.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenDensity
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesicsII

/-!
# Hyperbolic–Pythagorean Geodesics, cycle III: quadratic ball growth

The first cycle proved that the hyperbolic ball of radius `R` around `i` contains at least
`e^{R-2} - 1` Berggren nodes, and conjectured (sub-conjecture **C1-lite**) the true order
`e^{2R}`: the number of nodes should grow like the *hypotenuse*, not like its square root.

This file proves that conjecture.  The obstruction is arithmetic, not geometric: one has to
produce quadratically many *coprime* pairs of opposite parity, which requires a sieve.

## Main results

* `card_multiples_Ioc` : the exact count of multiples of `k` in an interval `(a, b]`.
* `sum_inv_sq_odd`, `sum_inv_odd` : two telescoping estimates,
  `∑_{i<n} 1/(2i+3)² ≤ 1/4` and `∑_{i<n} 1/(2i+3) ≤ √(2n+1) - 1`.
* `card_seedBox_lower` : **the sieve bound.**  For `K ≥ 256` the box
  `{m even, 2K < m ≤ 4K} × {n odd, 1 ≤ n ≤ 2K}` contains at least `K²/4` Euclid seeds.
* `hyperbolic_ball_quadratic_growth` : **C1-lite, closed.**  For every `K ≥ 256` the
  hyperbolic ball of radius `R = log K + 2` around the base point contains at least
  `e^{2R}/300` distinct Berggren nodes.  Since every node with hypotenuse `c` sits at
  distance `≈ ½ log c`, this is the true order of growth, and it shows definitively that
  geodesic search through the Berggren tree cannot beat exhaustive search: the ball that
  is guaranteed to contain a colliding pair for `N` already contains `≍ N` nodes.
-/

open HyperbolicBerggrenGeodesics

open Real UpperHalfPlane

noncomputable section

/-! ## Part A. Counting multiples -/



/-! ## Part B. Two telescoping estimates -/



/-! ## Part C. The sieve -/












/-! ## Part D. From the sieve to a quadratic lower bound -/



/-! ## Part E. Quadratic volume growth of hyperbolic balls (C1-lite, closed) -/

theorem HyperbolicBerggrenGeodesics.nodePoint_dist_le{K : ℕ} (hK : 256 ≤ K) {p : ℕ × ℕ} (hp : p ∈ seedBox K) :
    dist (nodePoint p) UpperHalfPlane.I ≤ Real.log K + 2 := by sorry
