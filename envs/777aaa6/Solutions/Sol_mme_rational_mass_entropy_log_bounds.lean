-- Prove2me | solution 1 for mme_rational_mass_entropy_log_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T11:51:48.161988+00:00
-- url     : https://prove2.me/submissions/e27e782f-75d1-4342-b24b-1aba1e0eb6f6

import Theorems.Thm_mme_rational_entropy_log_bounds
import Theorems.Thm_mme_regional_mass_entropy_algebra

open scoped BigOperators
open MME.RegionRate

/-- Logarithm bounds for normalized masses give homogeneous entropy bounds.
An empty mass vector needs no logarithm certificate and contributes zero. -/
theorem solution
    {W : Type*} [Fintype W] (x : W → ℚ) (hx : ∀ w, 0 ≤ x w)
    (lower upper : W → ℚ)
    (hlog : ∀ w, 0 < x w / ∑ v, x v →
      (lower w : ℝ) ≤ Real.log ((x w / ∑ v, x v : ℚ) : ℝ) ∧
        Real.log ((x w / ∑ v, x v : ℚ) : ℝ) ≤ (upper w : ℝ)) :
    (((∑ w, x w) * (-(∑ w, (x w / ∑ v, x v) * upper w)) : ℚ) : ℝ) ≤
        massEntropy (fun w => (x w : ℝ)) ∧
      massEntropy (fun w => (x w : ℝ)) ≤
        (((∑ w, x w) * (-(∑ w, (x w / ∑ v, x v) * lower w)) : ℚ) : ℝ) := by
  classical
  have hs : (0 : ℚ) ≤ ∑ w, x w := Finset.sum_nonneg (fun w _ => hx w)
  have hsR : (0 : ℝ) ≤ ∑ w, (x w : ℝ) := by exact_mod_cast hs
  by_cases hz : ∑ w, x w = 0
  · have hw : ∀ w, x w = 0 := by
      intro w
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hx v)).mp hz w
        (Finset.mem_univ w)
    simp [hw, massEntropy, entropy]
  · have hzR : ∑ w, (x w : ℝ) ≠ 0 := by exact_mod_cast hz
    rw [(mme_regional_mass_entropy_algebra (C := Unit) (W := W)).2.1
      (fun w => (x w : ℝ)) hzR]
    have h := mme_rational_entropy_log_bounds (fun w => x w / ∑ v, x v)
      (fun w => div_nonneg (hx w) hs) lower upper hlog
    push_cast at h ⊢
    exact ⟨mul_le_mul_of_nonneg_left h.1 hsR,
      mul_le_mul_of_nonneg_left h.2 hsR⟩


#print axioms solution
