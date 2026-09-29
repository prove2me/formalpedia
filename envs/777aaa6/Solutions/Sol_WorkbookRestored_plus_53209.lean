-- Prove2me | solution 1 for WorkbookRestored.plus_53209
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:24:50.862979+00:00
-- url     : https://prove2.me/submissions/1a8657d2-fc6f-439a-89b7-e3ac83e35fed

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_53209.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : tan (π / 8) = √2 - 1   := by
  have hs : 0 ≤ sin (π/8) := sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [pi_pos])
  have hc : 0 < cos (π/8) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos],by linarith [pi_pos]⟩
  have hsd := sin_two_mul (π/8)
  have hcd := cos_two_mul (π/8)
  rw [show 2*(π/8)=π/4 by ring,sin_pi_div_four] at hsd
  rw [show 2*(π/8)=π/4 by ring,cos_pi_div_four] at hcd
  have hq : (sin (π/8)/cos (π/8))^2 + 2*(sin (π/8)/cos (π/8)) = 1 := by
    field_simp
    nlinarith [sin_sq_add_cos_sq (π/8)]
  rw [tan_eq_sin_div_cos]
  nlinarith [div_nonneg hs hc.le,sq_sqrt (show (0:ℝ)≤2 by norm_num),sqrt_nonneg (2:ℝ)]
#print axioms solution
