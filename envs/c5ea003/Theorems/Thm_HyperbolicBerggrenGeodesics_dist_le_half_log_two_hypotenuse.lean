-- Prove2me | Theorems.Thm_HyperbolicBerggrenGeodesics_dist_le_half_log_two_hypotenuse
-- name    : HyperbolicBerggrenGeodesics.dist_le_half_log_two_hypotenuse
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:27:12.62698+00:00
-- url     : https://prove2.me/theorems/c28278d2-3953-41ee-8166-1491059ec143
-- title:
--   Sharp upper bound.
-- statement:
--   **Sharp upper bound.**  The distance never exceeds `½ log (2 (c+1))`.
--
--   ```lean
--   theorem HyperbolicBerggrenGeodesics.dist_le_half_log_two_hypotenuse{m n : ℕ} (hn : 0 < n) (hnm : n < m) :
--       dist (hpoint m n (lt_trans hn hnm)) UpperHalfPlane.I ≤
--         (1 / 2) * Real.log (2 * (((m : ℝ) ^ 2 + (n : ℝ) ^ 2) + 1)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/HyperbolicBerggrenGeodesicsII.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/HyperbolicBerggrenGeodesicsII.lean#L87

-- Thm stub generated from Geometry/HyperbolicBerggrenGeodesicsII.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesics
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesicsII

/-!
# Hyperbolic–Pythagorean Geodesics, cycle II

This file is the second research cycle built on
`Geometry.HyperbolicBerggrenGeodesics`.  It closes three of the open sub-conjectures
recorded at the end of that cycle and adds a genuinely new arithmetic pay-off.

## Main results

* `cosh_half_log`, `dist_ge_half_log_hypotenuse`, `dist_le_half_log_two_hypotenuse`,
  `trajectory_window` : **the sharpened logarithmic trajectory law.**  The previous
  cycle proved `|d - ½ log c| ≤ log 2`.  Here the two sides are separated and both are
  improved to the truth: the *lower* bound holds with **no additive constant at all**,
  `d ≥ ½ log c`, and the upper bound is `d ≤ ½ log (2 (c+1)) ≤ ½ log c + ½ log 2 + 1/(2c)`.
  So every Berggren node lies in the half-open annulus
  `½ log c ≤ d < ½ log c + ½ log 2 + o(1)` of width `½ log 2 ≈ 0.3466`, which matches the
  numerically observed residual range `[0.157, 0.30]`.
* `hpoint_injective`, `seed_point_injective` : distinct Euclid seeds give distinct
  points of `ℍ`, so the node count of the previous cycle is an honest point count.
* `vertGeodesic_energy`, `energy_lower_bound_sharp` : **the Cauchy–Schwarz energy bound
  is sharp** (sub-conjecture C3-lite).  For every `k > 0` and every displacement `t ≥ 0`
  there is a `k`-step trajectory with `dist (z 0) (z k) = t` and
  `pathEnergy z k = t²/k` exactly.
* `euler_gcd_product` : **a collision computes a complete splitting, not just one
  divisor.**  If `N` is odd and `N = a²+b² = c²+d²` with both representations primitive,
  then `gcd(N, ac+bd) · gcd(N, ad+bc) = N`.
* `berggren_collision_splits` : consequently two distinct Berggren nodes with the same
  hypotenuse `N` split `N = g · h` with `1 < g, h < N`; both factors are produced at once
  by the geometry.
* `exists_collision_gt`, `collision_hypotenuses_infinite` : **collisions exist at every
  scale.**  An explicit two-parameter family of colliding seed pairs
  `(20j+9, 10j+2)` and `(20j+7, 10j+6)`, both with hypotenuse `500j² + 400j + 85`, shows
  the set of hypotenuses carried by two distinct Berggren nodes is infinite, and the
  divisor extracted from the collision is computed exactly: it equals `5`.
-/

open HyperbolicBerggrenGeodesics

open Real UpperHalfPlane

noncomputable section

/-! ## Part A. The sharpened logarithmic trajectory law -/

theorem HyperbolicBerggrenGeodesics.dist_le_half_log_two_hypotenuse{m n : ℕ} (hn : 0 < n) (hnm : n < m) :
    dist (hpoint m n (lt_trans hn hnm)) UpperHalfPlane.I ≤
      (1 / 2) * Real.log (2 * (((m : ℝ) ^ 2 + (n : ℝ) ^ 2) + 1)) := by sorry
