-- Prove2me | solution 1 for WorkbookRestored.plus_6740
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:31:11.433349+00:00
-- url     : https://prove2.me/submissions/14f3d18b-2985-472a-8dd1-c8d503886969

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_6740.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) : sin (x + 2 * π) = sin x   := by
  simp [sin_add, sin_two_mul]
#print axioms solution
