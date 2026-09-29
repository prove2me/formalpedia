-- Prove2me | solution 1 for WorkbookRestored.plus_50659
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:08:46.222644+00:00
-- url     : https://prove2.me/submissions/d14d2f74-674b-43b5-b034-3a7653ca8741

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_50659.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x y : ℝ) : sinh (x + y) = sinh x * cosh y + sinh y * cosh x   := by
  simp [Real.sinh_add, add_mul, mul_add, mul_comm, mul_left_comm]
#print axioms solution
