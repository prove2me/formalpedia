-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.collision_gcd_three_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:31:07.978468+00:00
-- url     : https://prove2.me/submissions/4f7c7dae-1bd2-417f-b32e-5da543ad5772

-- Sol generated from Geometry/HyperbolicBerggrenGeodesicsII.lean
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





/-! ## Part B. Distinct seeds give distinct points -/



/-! ## Part C. Sharpness of the Cauchy–Schwarz energy bound (sub-conjecture C3-lite) -/







/-! ## Part D. A collision computes a *complete* splitting -/







/-! ## Part E. Collisions occur at every scale -/










open HyperbolicBerggrenGeodesics in
theorem solution{a b c d N : ℕ} (hodd : N % 2 = 1)
    (hab : Nat.Coprime a b) (hcd : Nat.Coprime c d)
    (h1 : a ^ 2 + b ^ 2 = N) :
    Nat.gcd (Nat.gcd N (a * c + b * d)) (a * d + b * c) = 1 := by
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have hpNP : p ∣ Nat.gcd N (a * c + b * d) := hpd.trans (Nat.gcd_dvd_left _ _)
  have hpN : p ∣ N := hpNP.trans (Nat.gcd_dvd_left _ _)
  have hpP : p ∣ a * c + b * d := hpNP.trans (Nat.gcd_dvd_right _ _)
  have hpQ : p ∣ a * d + b * c := hpd.trans (Nat.gcd_dvd_right _ _)
  -- move to `ℤ`, where the subtraction `a² - b²` makes sense
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hPZ : (p : ℤ) ∣ (a : ℤ) * c + (b : ℤ) * d := by exact_mod_cast Int.natCast_dvd_natCast.2 hpP
  have hQZ : (p : ℤ) ∣ (a : ℤ) * d + (b : ℤ) * c := by exact_mod_cast Int.natCast_dvd_natCast.2 hpQ
  have hNZ : (p : ℤ) ∣ (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by
    have : ((a ^ 2 + b ^ 2 : ℕ) : ℤ) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by push_cast; ring
    rw [← this, h1]
    exact Int.natCast_dvd_natCast.2 hpN
  have hc1 : (p : ℤ) ∣ (c : ℤ) * ((a : ℤ) ^ 2 - (b : ℤ) ^ 2) := by
    have hid : (c : ℤ) * ((a : ℤ) ^ 2 - (b : ℤ) ^ 2)
        = (a : ℤ) * ((a : ℤ) * c + (b : ℤ) * d) - (b : ℤ) * ((a : ℤ) * d + (b : ℤ) * c) := by ring
    rw [hid]
    exact dvd_sub (hPZ.mul_left _) (hQZ.mul_left _)
  have hd1 : (p : ℤ) ∣ (d : ℤ) * ((a : ℤ) ^ 2 - (b : ℤ) ^ 2) := by
    have hid : (d : ℤ) * ((a : ℤ) ^ 2 - (b : ℤ) ^ 2)
        = (a : ℤ) * ((a : ℤ) * d + (b : ℤ) * c) - (b : ℤ) * ((a : ℤ) * c + (b : ℤ) * d) := by ring
    rw [hid]
    exact dvd_sub (hQZ.mul_left _) (hPZ.mul_left _)
  obtain ⟨u, v, huv⟩ : IsCoprime (c : ℤ) (d : ℤ) := Nat.isCoprime_iff_coprime.2 hcd
  have hdiff : (p : ℤ) ∣ (a : ℤ) ^ 2 - (b : ℤ) ^ 2 := by
    have hid : (a : ℤ) ^ 2 - (b : ℤ) ^ 2
        = u * ((c : ℤ) * ((a : ℤ) ^ 2 - (b : ℤ) ^ 2))
          + v * ((d : ℤ) * ((a : ℤ) ^ 2 - (b : ℤ) ^ 2)) := by
      have : (u * (c : ℤ) + v * (d : ℤ)) * ((a : ℤ) ^ 2 - (b : ℤ) ^ 2)
          = (a : ℤ) ^ 2 - (b : ℤ) ^ 2 := by rw [huv]; ring
      linarith [this]
    rw [hid]
    exact dvd_add (hc1.mul_left _) (hd1.mul_left _)
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨t, ht⟩ := hpN
    omega
  have hpnot2 : ¬ (p : ℤ) ∣ 2 := by
    intro hcon
    have hd2 : p ∣ 2 := by exact_mod_cast hcon
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd2)
  have hpa : (p : ℤ) ∣ (a : ℤ) := by
    have h2a : (p : ℤ) ∣ 2 * (a : ℤ) ^ 2 := by
      have : 2 * (a : ℤ) ^ 2 = ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) + ((a : ℤ) ^ 2 - (b : ℤ) ^ 2) := by ring
      rw [this]; exact dvd_add hNZ hdiff
    rcases hpZ.dvd_mul.1 h2a with h | h
    · exact absurd h hpnot2
    · exact hpZ.dvd_of_dvd_pow h
  have hpb : (p : ℤ) ∣ (b : ℤ) := by
    have h2b : (p : ℤ) ∣ 2 * (b : ℤ) ^ 2 := by
      have : 2 * (b : ℤ) ^ 2 = ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) - ((a : ℤ) ^ 2 - (b : ℤ) ^ 2) := by ring
      rw [this]; exact dvd_sub hNZ hdiff
    rcases hpZ.dvd_mul.1 h2b with h | h
    · exact absurd h hpnot2
    · exact hpZ.dvd_of_dvd_pow h
  have hpa' : p ∣ a := by exact_mod_cast hpa
  have hpb' : p ∣ b := by exact_mod_cast hpb
  have : p ∣ 1 := hab ▸ Nat.dvd_gcd hpa' hpb'
  exact Nat.Prime.one_lt hp |>.ne' (Nat.dvd_one.1 this)
