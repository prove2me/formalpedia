-- Prove2me | solution 1 for WorkbookRestored.plus_13953
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:10.766553+00:00
-- url     : https://prove2.me/submissions/da367170-90f1-4279-b0bc-e68bc6f07cdd

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_13953.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (α : ℝ) (hα : 0 ≤ α) : 0 ≤ Real.log (1 + α) ∧ Real.log (1 + α) ≤ α   := by
  refine' ⟨log_nonneg (by linarith), by linarith [log_le_sub_one_of_pos (show (0 : ℝ) < 1 + α by linarith)]⟩
#print axioms solution
