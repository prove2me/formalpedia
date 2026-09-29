-- Prove2me | solution 1 for WorkbookRestored.plus_56
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:17:33.315405+00:00
-- url     : https://prove2.me/submissions/1fbfc8cf-ecc3-46c6-a62a-14b0cdf1f33d

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_56.
   Draft repair: only required imports and namespaces are restored. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : sin (π / 4) = cos (π / 4) ∧ sin (π / 4) = 1 / Real.sqrt 2 ∧ cos (π / 4) = 1 / Real.sqrt 2   := by
  rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
  have h : Real.sqrt 2 / 2 = 1 / Real.sqrt 2 := by
    have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    apply (div_eq_div_iff (by norm_num) hs).2
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact ⟨rfl, h, h⟩
#print axioms solution
