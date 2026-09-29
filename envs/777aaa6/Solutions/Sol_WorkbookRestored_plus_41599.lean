-- Prove2me | solution 1 for WorkbookRestored.plus_41599
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:05:03.901985+00:00
-- url     : https://prove2.me/submissions/f2a169dd-3a12-45ad-a700-8b802a7f5339

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_41599.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx: 0 ≤ x ∧ x ≤ 1) : (exp x - 1) / (exp x - x) ≥ 0   := by
  refine' div_nonneg (sub_nonneg_of_le _) (sub_nonneg_of_le _)
  all_goals linarith [add_one_le_exp x]
#print axioms solution
