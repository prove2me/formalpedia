-- Prove2me | solution 1 for WorkbookRestored.plus_68742
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:18.095582+00:00
-- url     : https://prove2.me/submissions/89b4cfc8-2900-471e-9e63-cac838bdb317

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_68742.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x y : ℝ) : cosh (x + y) = cosh x * cosh y + sinh x * sinh y   := by
  simp [Real.cosh_add, Real.sinh_add, exp_add, mul_add, mul_comm, mul_left_comm]
#print axioms solution
