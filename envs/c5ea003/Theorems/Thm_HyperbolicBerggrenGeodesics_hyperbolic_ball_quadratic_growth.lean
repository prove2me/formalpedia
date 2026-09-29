-- Prove2me | Theorems.Thm_HyperbolicBerggrenGeodesics_hyperbolic_ball_quadratic_growth
-- name    : HyperbolicBerggrenGeodesics.hyperbolic_ball_quadratic_growth
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:27:45.620489+00:00
-- url     : https://prove2.me/theorems/e2b251a0-3471-4115-b0dc-6f132022968f
-- title:
--   C1-lite, closed: quadratic volume growth.
-- statement:
--   **C1-lite, closed: quadratic volume growth.**
--   For every `K ≥ 256` there are at least `e^{2R}/300` distinct Berggren nodes inside the
--   hyperbolic ball of radius `R = log K + 2` around the base point `i`.
--
--   Combined with `dist_ge_half_log_hypotenuse` (`d ≥ ½ log c`), this pins the growth exponent:
--   the ball of radius `R` contains `≍ e^{2R}` nodes, i.e. as many as there are hypotenuses of
--   size `e^{2R}`.  Geodesic energy minimisation therefore cannot factor `N` faster than
--   exhaustive search over the collision fibre.
--
--   ```lean
--   theorem HyperbolicBerggrenGeodesics.hyperbolic_ball_quadratic_growth{K : ℕ} (hK : 256 ≤ K) :
--       ∃ (R : ℝ) (S : Finset ℍ), R = Real.log K + 2 ∧
--         Real.exp (2 * R) / 300 ≤ (S.card : ℝ) ∧
--         ∀ z ∈ S, dist z UpperHalfPlane.I ≤ R := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/HyperbolicBerggrenDensity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/HyperbolicBerggrenDensity.lean#L397

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

theorem HyperbolicBerggrenGeodesics.hyperbolic_ball_quadratic_growth{K : ℕ} (hK : 256 ≤ K) :
    ∃ (R : ℝ) (S : Finset ℍ), R = Real.log K + 2 ∧
      Real.exp (2 * R) / 300 ≤ (S.card : ℝ) ∧
      ∀ z ∈ S, dist z UpperHalfPlane.I ≤ R := by sorry
