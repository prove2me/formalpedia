-- Prove2me | solution 1 for mme_mass_entropy_dyadic_upper
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T07:04:41.190762+00:00
-- url     : https://prove2.me/submissions/09c91bf6-e270-4ac3-853c-cf3a67165b7e

import Theorems.Thm_mme_entropy_dyadic_bounds
import Theorems.Thm_mme_regional_mass_entropy_algebra

open scoped BigOperators
open MME.RegionRate

/-- Dyadic entropy bounds also apply to unnormalized nonnegative masses,
including an identically zero mass vector. -/
theorem solution {W : Type*} [Fintype W]
    (x : W → ℝ) (hx : ∀ w, 0 ≤ x w) (k : W → ℕ) :
    massEntropy x ≤ (∑ w, x w) *
      ∑ w, (x w / ∑ v, x v) *
        ((k w : ℝ) * (693147181 / 1000000000 : ℝ) - 1 +
          (2 ^ k w * (x w / ∑ v, x v))⁻¹) := by
  classical
  have hs : 0 ≤ ∑ w, x w := Finset.sum_nonneg (fun w _ => hx w)
  by_cases hz : ∑ w, x w = 0
  · have hw : ∀ w, x w = 0 := by
      intro w
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hx v)).mp hz w (Finset.mem_univ w)
    simp [hw, massEntropy, entropy]
  · rw [(mme_regional_mass_entropy_algebra (C := Unit) (W := W)).2.1 x hz]
    exact mul_le_mul_of_nonneg_left
      (mme_entropy_dyadic_bounds (fun w => x w / ∑ v, x v)
        (fun w => div_nonneg (hx w) hs) k).2 hs


#print axioms solution
