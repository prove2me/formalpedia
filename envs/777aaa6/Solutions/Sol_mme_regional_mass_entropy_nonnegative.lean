-- Prove2me | solution 1 for mme_regional_mass_entropy_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T20:34:04.227152+00:00
-- url     : https://prove2.me/submissions/a11b6337-0402-42f5-865b-9cdd30327f62

import Theorems.Thm_mme_regional_mass_entropy_algebra
import Mathlib
open BigOperators MME.RegionRate
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem solution {W : Type*} [Fintype W] (x : W → ℝ) (hx : ∀ w, 0 ≤ x w) :
    0 ≤ massEntropy x := by
  classical
  have hs : 0 ≤ ∑ w, x w := Finset.sum_nonneg (fun w _ ↦ hx w)
  by_cases hz : ∑ w, x w = 0
  · have he : ∀ w, x w = 0 := fun w ↦
      (Finset.sum_eq_zero_iff_of_nonneg (fun w _ ↦ hx w)).mp hz w (Finset.mem_univ w)
    simp [massEntropy,entropy,he]
  · rw [(mme_regional_mass_entropy_algebra (C := Unit) (W := W)).2.1 x hz]
    apply mul_nonneg hs
    unfold entropy
    apply Finset.sum_nonneg
    intro w hw
    apply Real.negMulLog_nonneg (div_nonneg (hx w) hs)
    apply (div_le_one (lt_of_le_of_ne hs (Ne.symm hz))).mpr
    exact Finset.single_le_sum (fun v _ ↦ hx v) hw
