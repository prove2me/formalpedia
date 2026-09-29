-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.euler_gcd_product
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:32:32.120077+00:00
-- url     : https://prove2.me/submissions/b595abcb-6be3-4833-8fd2-52eea94ed74b

-- Sol generated from Geometry/HyperbolicBerggrenGeodesicsII.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesics
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesicsII
import Theorems.Thm_HyperbolicBerggrenGeodesics_collision_gcd_three_eq_one

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

/-- Euler's product identity `(ac+bd)(ad+bc) = N (ab+cd)` for two representations of `N`
as a sum of two squares. -/
theorem euler_cross_product {a b c d N : ℕ} (h1 : a ^ 2 + b ^ 2 = N) (h2 : c ^ 2 + d ^ 2 = N) :
    (a * c + b * d) * (a * d + b * c) = N * (a * b + c * d) := by
  have hexp : (a * c + b * d) * (a * d + b * c)
      = (a ^ 2 + b ^ 2) * (c * d) + (c ^ 2 + d ^ 2) * (a * b) := by ring
  rw [h1, h2] at hexp
  rw [hexp]; ring






/-! ## Part E. Collisions occur at every scale -/










open HyperbolicBerggrenGeodesics in
theorem solution{a b c d N : ℕ} (hodd : N % 2 = 1)
    (hab : Nat.Coprime a b) (hcd : Nat.Coprime c d)
    (h1 : a ^ 2 + b ^ 2 = N) (h2 : c ^ 2 + d ^ 2 = N) :
    Nat.gcd N (a * c + b * d) * Nat.gcd N (a * d + b * c) = N := by
  set P := a * c + b * d with hP
  set Q := a * d + b * c with hQ
  set S := a * b + c * d with hS
  have hPQ : P * Q = N * S := euler_cross_product h1 h2
  have hstep : P * Nat.gcd N Q = N * Nat.gcd P S := by
    rw [← Nat.gcd_mul_left P N Q, mul_comm P N, hPQ, Nat.gcd_mul_left N P S]
  have hcop : Nat.gcd (Nat.gcd N Q) (Nat.gcd P S) = 1 := by
    have hdvd : Nat.gcd (Nat.gcd N Q) (Nat.gcd P S) ∣ Nat.gcd (Nat.gcd N P) Q := by
      refine Nat.dvd_gcd (Nat.dvd_gcd ?_ ?_) ?_
      · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
      · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
      · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
    exact Nat.eq_one_of_dvd_one (collision_gcd_three_eq_one hodd hab hcd h1 ▸ hdvd)
  calc Nat.gcd N P * Nat.gcd N Q
      = Nat.gcd (N * Nat.gcd N Q) (P * Nat.gcd N Q) := (Nat.gcd_mul_right N (Nat.gcd N Q) P).symm
    _ = Nat.gcd (N * Nat.gcd N Q) (N * Nat.gcd P S) := by rw [hstep]
    _ = N * Nat.gcd (Nat.gcd N Q) (Nat.gcd P S) := Nat.gcd_mul_left _ _ _
    _ = N := by rw [hcop, mul_one]
