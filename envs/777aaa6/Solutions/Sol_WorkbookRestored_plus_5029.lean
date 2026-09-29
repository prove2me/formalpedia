-- Prove2me | solution 1 for WorkbookRestored.plus_5029
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:31:06.02356+00:00
-- url     : https://prove2.me/submissions/10be5710-e3a3-4a90-a974-5af1625b9469

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_5029.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a : ℝ) : 3 * Real.sin a - 4 * (Real.sin a)^3 = Real.sin (3 * a)   := by
  simp [Real.sin_three_mul, sub_eq_add_neg, add_comm]
#print axioms solution
