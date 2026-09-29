-- Prove2me | solution 1 for WorkbookRestored.plus_65632
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:12.980955+00:00
-- url     : https://prove2.me/submissions/d25e64e2-c32d-4c94-b102-00a2265e9b4b

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_65632.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (v : ℝ) (h : v < 0) : v / (1 + exp (- v)) < 0   := by
  refine' div_neg_of_neg_of_pos h (add_pos_of_pos_of_nonneg zero_lt_one (le_of_lt (exp_pos _)))
#print axioms solution
