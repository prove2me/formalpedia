-- Prove2me | solution 1 for WorkbookRestored.plus_26180
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:01:52.775984+00:00
-- url     : https://prove2.me/submissions/f6ce8384-4213-4c70-a04e-021fc1362750

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_26180.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x a b : ℝ) (hx : x > 0) (hab : a > 0 ∧ b > 0) : Real.logb x a - Real.logb x b = Real.logb x (a / b)   := by
  rw [logb_div hab.1.ne' hab.2.ne', sub_eq_add_neg]
#print axioms solution
