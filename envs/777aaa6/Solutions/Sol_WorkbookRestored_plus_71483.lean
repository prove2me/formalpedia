-- Prove2me | solution 1 for WorkbookRestored.plus_71483
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:20.362344+00:00
-- url     : https://prove2.me/submissions/3720dce1-10c9-4a22-a700-aaba6f298b2d

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_71483.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x y : ℝ) (h₁ : Real.cos x = Real.cos y) (h₂ : Real.sin x = -Real.sin y) : (Real.sin ((x + y) / 2))^2 = 0   := by
  rw [sin_sq, cos_sq, ← sub_eq_zero]
  rw [show (2 : ℝ) * ((x + y) / 2) = x + y by ring, cos_add, h₁, h₂]
  linarith [cos_sq_add_sin_sq y]
#print axioms solution
