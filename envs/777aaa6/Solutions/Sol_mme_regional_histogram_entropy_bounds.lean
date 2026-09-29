-- Prove2me | solution 1 for mme_regional_histogram_entropy_bounds
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T20:34:06.511416+00:00
-- url     : https://prove2.me/submissions/683a7de2-2704-49e8-bd07-6845693df36e

import Theorems.Thm_mme_regional_mass_entropy_algebra
import Theorems.Thm_mme_prescribed_cell_histogram_entropy_bounds
import Mathlib
open BigOperators MME.RegionRate MME.RegionRealization MME.RecursiveYZ
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem solution {C W : Type*} [Fintype C] [Fintype W]
    (mu : C → W → ℕ) (S : ℕ) (hS : ∀ c, ∑ w, mu c w ≤ S) :
    (histogramNumber mu : ℝ) ≤ Real.exp (∑ c, massEntropy (fun w ↦ (mu c w : ℝ))) ∧
    Real.exp (∑ c, massEntropy (fun w ↦ (mu c w : ℝ))) ≤
      (6 * ((S : ℝ) + 1)) ^ (Fintype.card C * Fintype.card W) * histogramNumber mu := by
  have h := mme_prescribed_cell_histogram_entropy_bounds mu 1 (by omega)
  simp only [Nat.mul_one,Nat.cast_one,one_mul] at h
  rw [(mme_regional_mass_entropy_algebra (C := C) (W := W)).2.2 mu] at h
  refine ⟨h.1,h.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  unfold errorFactor
  rw [Nat.mul_comm, pow_mul]
  have he : (∏ _c : C, (6 * ((S : ℝ) + 1)) ^ Fintype.card W) =
      ((6 * ((S : ℝ) + 1)) ^ Fintype.card W) ^ Fintype.card C := by simp
  rw [← he]
  apply Finset.prod_le_prod
  · intro c _; positivity
  · intro c _
    apply pow_le_pow_left₀ (by positivity)
    simp only [Nat.mul_one,Nat.cast_add,Nat.cast_one]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_right (hS c) 1) (by norm_num)
