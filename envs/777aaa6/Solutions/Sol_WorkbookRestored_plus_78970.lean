-- Prove2me | solution 1 for WorkbookRestored.plus_78970
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:31.468905+00:00
-- url     : https://prove2.me/submissions/1b34848c-ce7e-4cfd-95e1-2f2fc4a977b6

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_78970.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x y : ℝ) (h₁ : y = Real.sin (x + Real.pi / 4)) : Real.sin (2 * x) = 2 * y ^ 2 - 1   := by
  rw [h₁,sin_add,sin_two_mul,cos_pi_div_four,sin_pi_div_four]
  nlinarith [sq_sqrt (show (0:ℝ)≤2 by norm_num),sin_sq_add_cos_sq x]
#print axioms solution
