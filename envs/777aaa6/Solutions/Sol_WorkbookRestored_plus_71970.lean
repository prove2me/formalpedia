-- Prove2me | solution 1 for WorkbookRestored.plus_71970
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:21.973762+00:00
-- url     : https://prove2.me/submissions/c9242048-97c4-4930-8ea3-181831c88d85

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_71970.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a b : ℝ) (u v : ℝ) : a * sin u + b * sin (u + v) = (a + b * cos v) * sin u + (b * sin v) * cos u   := by
  simp [Real.sin_add, mul_add, add_mul]
  ring
#print axioms solution
