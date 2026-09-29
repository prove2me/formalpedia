-- Prove2me | solution 1 for WorkbookRestored.plus_19213
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:31.934489+00:00
-- url     : https://prove2.me/submissions/097f95f3-359e-4395-9a22-af0470d64444

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_19213.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) : Real.sin (3*x) = 4*Real.sin x * Real.sin (π/3 - x) * Real.sin (π/3 + x)   := by
  rw [sin_three_mul, sin_sub, sin_add, sin_pi_div_three, cos_pi_div_three]
  linear_combination -3 * sin x * (sin_sq_add_cos_sq x) - sin x * cos x^2 * (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3))
#print axioms solution
