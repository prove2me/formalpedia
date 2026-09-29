-- Prove2me | solution 1 for Bridges.AlexanderTorus.alexander_dvd_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T12:33:49.348907+00:00
-- url     : https://prove2.me/submissions/65314684-46e8-4cf6-937d-6ad0ea9d78a3

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
open Bridges.AlexanderTorus Polynomial in
theorem solution {d M : ℕ} (hM : Odd M) (hd1 : 1 < d) (hM1 : 1 < M) (hdvd : d ∣ M) :
    alexander d ∣ alexander M := by
  -- geometric sum: for odd `N`, `(X + 1) · alexander N = X^N + 1`
  have hgeom : ∀ N : ℕ, Odd N → (X + 1 : Polynomial ℤ) * alexander N = X ^ N + 1 := by
    intro N hN
    have h1 : alexander N = ∑ i ∈ Finset.range N, (-X : Polynomial ℤ) ^ i := by
      rw [alexander]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [neg_pow (X : Polynomial ℤ) i]
    rw [h1]
    have h2 := geom_sum_mul (-X : Polynomial ℤ) N
    rw [hN.neg_pow] at h2
    linear_combination -h2
  obtain ⟨k, rfl⟩ := hdvd
  have hd : Odd d := Nat.Odd.of_mul_left hM
  have hk : Odd k := Nat.Odd.of_mul_right hM
  have hX1 : (X + 1 : Polynomial ℤ) ≠ 0 := by
    have := Polynomial.X_add_C_ne_zero (1 : ℤ)
    simpa using this
  rw [← mul_dvd_mul_iff_left hX1, hgeom d hd, hgeom (d * k) hM, pow_mul]
  simpa using Odd.add_dvd_pow_add_pow (X ^ d : Polynomial ℤ) 1 hk
