-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.berggren_collision_splits
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:33:53.974998+00:00
-- url     : https://prove2.me/submissions/77652352-1b27-43c3-8450-35a440a230c4

-- Sol generated from Geometry/HyperbolicBerggrenGeodesicsII.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesics
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesicsII
import Theorems.Thm_HyperbolicBerggrenGeodesics_berggren_collision_factors
import Theorems.Thm_HyperbolicBerggrenGeodesics_euler_gcd_product

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


/-- Squares do not change parity. -/
theorem sq_mod_two (x : ℕ) : x ^ 2 % 2 = x % 2 := by
  conv_lhs => rw [Nat.pow_mod]
  rcases Nat.mod_two_eq_zero_or_one x with h | h
  · rw [h]
  · rw [h]

/-- The hypotenuse of a Euclid seed is odd. -/
theorem seed_hypotenuse_odd {m n : ℕ} (h : IsSeed m n) : (m ^ 2 + n ^ 2) % 2 = 1 := by
  have hm := sq_mod_two m
  have hn := sq_mod_two n
  have hp := h.parity
  omega




/-! ## Part E. Collisions occur at every scale -/










open HyperbolicBerggrenGeodesics in
theorem solution{m₁ n₁ m₂ n₂ N : ℕ} (h₁ : IsSeed m₁ n₁) (h₂ : IsSeed m₂ n₂)
    (hN₁ : m₁ ^ 2 + n₁ ^ 2 = N) (hN₂ : m₂ ^ 2 + n₂ ^ 2 = N) (hne : (m₁, n₁) ≠ (m₂, n₂)) :
    Nat.gcd N (m₁ * m₂ + n₁ * n₂) * Nat.gcd N (m₁ * n₂ + n₁ * m₂) = N ∧
      1 < Nat.gcd N (m₁ * m₂ + n₁ * n₂) ∧ Nat.gcd N (m₁ * m₂ + n₁ * n₂) < N ∧
      1 < Nat.gcd N (m₁ * n₂ + n₁ * m₂) ∧ Nat.gcd N (m₁ * n₂ + n₁ * m₂) < N := by
  have hodd : N % 2 = 1 := hN₁ ▸ seed_hypotenuse_odd h₁
  have hprod := euler_gcd_product hodd h₁.cop h₂.cop hN₁ hN₂
  obtain ⟨hlow, hhigh⟩ := berggren_collision_factors h₁ h₂ hN₁ hN₂ hne
  have hNpos : 0 < N := by omega
  refine ⟨hprod, hlow, hhigh, ?_, ?_⟩
  · -- if the second factor were `0` or `1`, the first would be `0` or `N`
    rcases Nat.eq_zero_or_pos (Nat.gcd N (m₁ * n₂ + n₁ * m₂)) with hz | hpos
    · rw [hz, mul_zero] at hprod; omega
    · rcases Nat.lt_or_ge 1 (Nat.gcd N (m₁ * n₂ + n₁ * m₂)) with hlt | hle
      · exact hlt
      · exfalso
        have hone : Nat.gcd N (m₁ * n₂ + n₁ * m₂) = 1 := by omega
        rw [hone, mul_one] at hprod
        omega
  · -- likewise the second factor cannot be all of `N`
    have hle : Nat.gcd N (m₁ * n₂ + n₁ * m₂) ≤ N :=
      Nat.le_of_dvd hNpos (Nat.gcd_dvd_left _ _)
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      rw [h] at hprod
      have hone : Nat.gcd N (m₁ * m₂ + n₁ * n₂) = 1 :=
        Nat.eq_of_mul_eq_mul_right hNpos (by rw [hprod, one_mul])
      omega
