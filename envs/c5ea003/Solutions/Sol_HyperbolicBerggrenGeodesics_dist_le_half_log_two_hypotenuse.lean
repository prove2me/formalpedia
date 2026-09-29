-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.dist_le_half_log_two_hypotenuse
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:58:15.579717+00:00
-- url     : https://prove2.me/submissions/f7c80046-3348-4f79-867a-61b0d0e5c8ce

-- Sol generated from Geometry/HyperbolicBerggrenGeodesicsII.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesics
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesicsII
import Theorems.Thm_HyperbolicBerggrenGeodesics_cosh_dist_hpoint_I
import Theorems.Thm_HyperbolicBerggrenGeodesics_log_cosh_sandwich

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





/-! ## Part B. Distinct seeds give distinct points -/



/-! ## Part C. Sharpness of the Cauchy–Schwarz energy bound (sub-conjecture C3-lite) -/







/-! ## Part D. A collision computes a *complete* splitting -/







/-! ## Part E. Collisions occur at every scale -/










open HyperbolicBerggrenGeodesics in
theorem solution{m n : ℕ} (hn : 0 < n) (hnm : n < m) :
    dist (hpoint m n (lt_trans hn hnm)) UpperHalfPlane.I ≤
      (1 / 2) * Real.log (2 * (((m : ℝ) ^ 2 + (n : ℝ) ^ 2) + 1)) := by
  have hm : 0 < m := lt_trans hn hnm
  have hM : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hN : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmn : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hnm
  set c : ℝ := (m : ℝ) ^ 2 + (n : ℝ) ^ 2 with hcdef
  have hcpos : 0 < c := by positivity
  set d := dist (hpoint m n hm) UpperHalfPlane.I with hd
  have hd0 : 0 ≤ d := dist_nonneg
  have hcosh : Real.cosh d = (c + 1) / (2 * m) := by rw [hd, cosh_dist_hpoint_I]
  obtain ⟨-, hhigh⟩ := log_cosh_sandwich hd0
  have h2c : 2 * Real.cosh d = (c + 1) / (m : ℝ) := by rw [hcosh]; field_simp
  -- `2 m² ≥ c + 1`, hence `((c+1)/m)² ≤ 2 (c+1)`
  have hm2 : c + 1 ≤ 2 * (m : ℝ) ^ 2 := by nlinarith
  have hkey : ((c + 1) / (m : ℝ)) ^ 2 ≤ 2 * (c + 1) := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    nlinarith
  have hpos : (0 : ℝ) < (c + 1) / (m : ℝ) := by positivity
  have hlog : Real.log ((c + 1) / (m : ℝ)) ≤ (1 / 2) * Real.log (2 * (c + 1)) := by
    have h1 : Real.log (((c + 1) / (m : ℝ)) ^ 2) ≤ Real.log (2 * (c + 1)) :=
      Real.log_le_log (by positivity) hkey
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  rw [h2c] at hhigh
  linarith
