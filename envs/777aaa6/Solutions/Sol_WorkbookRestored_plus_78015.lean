-- Prove2me | solution 1 for WorkbookRestored.plus_78015
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:30.015902+00:00
-- url     : https://prove2.me/submissions/81a67e48-5e60-4498-9043-46e6209af98f

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_78015.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (α : ℝ) (h₁ : 0 ≤ α) (h₂ : α ≤ π/2) (h₃ : cos α = 60/61) : sin (α/2) = √122 / 122   := by
  have hs : 0 ≤ sin (α/2) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos])
  have hc := cos_two_mul (α/2)
  rw [show 2*(α/2)=α by ring,h₃] at hc
  have hp := sin_sq_add_cos_sq (α/2)
  have hr := sq_sqrt (show (0:ℝ)≤122 by norm_num)
  have hn := sqrt_nonneg (122:ℝ)
  nlinarith
#print axioms solution
