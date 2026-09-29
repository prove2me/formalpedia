-- Prove2me | solution 1 for WorkbookRestored.plus_24283
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:01:45.767138+00:00
-- url     : https://prove2.me/submissions/11dc0afd-17cb-4428-bf61-a75ce704627f

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_24283.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (A B C : ℝ) (hx: A + B + C = π) : (sin A)^2 + (sin B)^2 + (sin C)^2 = 2*(1 + cos A * cos B * cos C)   := by
  have : C = π - (A + B) := by linarith
  simp [this, sin_sq, cos_add, cos_sub]
  nlinarith [cos_sq_add_sin_sq A, cos_sq_add_sin_sq B, cos_sq_add_sin_sq C]
#print axioms solution
