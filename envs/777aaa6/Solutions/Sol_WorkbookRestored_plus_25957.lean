-- Prove2me | solution 1 for WorkbookRestored.plus_25957
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:01:50.880279+00:00
-- url     : https://prove2.me/submissions/ef42815b-67b1-4bef-bae2-c8b18da58b84

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_25957.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : Real.sin (π / 11) ≠ 0   := by
  have h : 0 < π / 11 := div_pos pi_pos (by norm_num)
  nlinarith [sin_pos_of_pos_of_lt_pi h (by linarith)]
#print axioms solution
