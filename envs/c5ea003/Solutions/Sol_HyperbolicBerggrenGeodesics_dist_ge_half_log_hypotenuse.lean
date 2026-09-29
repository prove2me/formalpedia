-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.dist_ge_half_log_hypotenuse
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:23:36.708683+00:00
-- url     : https://prove2.me/submissions/6547c246-b583-4d0c-8083-706bf32b463b

-- Sol generated from Geometry/HyperbolicBerggrenGeodesicsII.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesics
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesicsII
import Theorems.Thm_HyperbolicBerggrenGeodesics_cosh_dist_hpoint_I

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

/-- `cosh (½ log c) = (c+1)/(2√c)` for `c > 0`: the level sets of the hyperbolic distance
from `i` are exactly the level sets of `(c+1)/(2m)`. -/
theorem cosh_half_log {c : ℝ} (hc : 0 < c) :
    Real.cosh ((1 / 2) * Real.log c) = (c + 1) / (2 * Real.sqrt c) := by
  have hsq : Real.sqrt c = Real.exp ((1 / 2) * Real.log c) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hc]
    ring_nf
  have hspos : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hss : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  rw [Real.cosh_eq, ← hsq, Real.exp_neg, ← hsq]
  field_simp
  linarith [hss]




/-! ## Part B. Distinct seeds give distinct points -/



/-! ## Part C. Sharpness of the Cauchy–Schwarz energy bound (sub-conjecture C3-lite) -/







/-! ## Part D. A collision computes a *complete* splitting -/







/-! ## Part E. Collisions occur at every scale -/










open HyperbolicBerggrenGeodesics in
theorem solution{m n : ℕ} (hn : 0 < n) (hnm : n < m) :
    (1 / 2) * Real.log ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ≤
      dist (hpoint m n (lt_trans hn hnm)) UpperHalfPlane.I := by
  have hm : 0 < m := lt_trans hn hnm
  have hM : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hN : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set c : ℝ := (m : ℝ) ^ 2 + (n : ℝ) ^ 2 with hcdef
  have hcpos : 0 < c := by positivity
  set d := dist (hpoint m n hm) UpperHalfPlane.I with hd
  have hd0 : 0 ≤ d := dist_nonneg
  have hcosh : Real.cosh d = (c + 1) / (2 * m) := by rw [hd, cosh_dist_hpoint_I]
  -- `m ≤ √c`
  have hsq : Real.sqrt c ≥ (m : ℝ) := by
    rw [show (m : ℝ) = Real.sqrt ((m : ℝ) ^ 2) from (Real.sqrt_sq hM.le).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hspos : 0 < Real.sqrt c := Real.sqrt_pos.2 hcpos
  have hkey : Real.cosh ((1 / 2) * Real.log c) ≤ Real.cosh d := by
    rw [cosh_half_log hcpos, hcosh]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    linarith
  have := (Real.cosh_le_cosh).1 hkey
  calc (1 / 2) * Real.log c ≤ |(1 / 2) * Real.log c| := le_abs_self _
    _ ≤ |d| := this
    _ = d := abs_of_nonneg hd0
