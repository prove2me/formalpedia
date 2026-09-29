-- Prove2me | solution 1 for mme_boundary_table_weight_rate_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:35:35.200536+00:00
-- url     : https://prove2.me/submissions/eaaf5691-1fbc-45f8-b7e6-58f3a732cfbe

import Theorems.Thm_mme_boundary_profile_volume_mass_entropy

open scoped BigOperators
open MME MME.RegionRate MME.RegionRealization MME.CompleteSplit MME.RecursiveYZ.Boundary

/-- An already weighted boundary table bounds the physical child rate with
a uniform loss, including the zero-exponent endpoint. -/
theorem solution {ell L : ℕ}
    (D k : ℕ) (hD : 0 < D)
    (B : Profile ell L) (z : Fin 3) (mu : Fin 3 → CompleteWord ell → ℕ)
    (hmu : ∀ i w, mu i w = B.mu z i w)
    (tau delta bound : ℝ) (htau1 : tau ≤ 1)
    (hdelta : 0 ≤ delta)
    (hvolume : (D : ℝ) ^ 4 * bound ≤ 6 * tau *
      (massEntropy (fun w ↦ (mu (z + 1) w : ℝ)) +
        ((∑ w, mu (z + 1) w * ones w : ℕ) : ℝ) * Real.log 5)) :
    ((2 * k : ℕ) : ℝ) * (D : ℝ) ^ 4 * (bound - 6 * delta) ≤
      6 * tau * ((2 * k : ℕ) : ℝ) *
        ((L : ℝ) * Real.log 2 *
          mme_modern_entropyBits (fun w ↦ (B.count w : ℝ) / (L : ℝ)) +
          ((∑ w, B.count w * ones w : ℕ) : ℝ) * Real.log 5 - delta) := by
  rw [mme_boundary_profile_volume_mass_entropy B z mu hmu]
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hD4 : (1 : ℝ) ≤ (D : ℝ) ^ 4 := one_le_pow₀ hD1
  have hloss : 6 * tau * delta ≤ 6 * (D : ℝ) ^ 4 * delta := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (htau1.trans hD4) (by norm_num)) hdelta
  have h := mul_le_mul_of_nonneg_left (sub_le_sub hvolume hloss)
    (show 0 ≤ ((2 * k : ℕ) : ℝ) by positivity)
  convert h using 1 <;> ring


#print axioms solution
