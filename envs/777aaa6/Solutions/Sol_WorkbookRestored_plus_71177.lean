-- Prove2me | solution 1 for WorkbookRestored.plus_71177
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:19.599865+00:00
-- url     : https://prove2.me/submissions/d8986d09-4ae1-4662-80c5-8070081d421b

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_71177.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∃ x : ℝ, 0 < x ∧ x ≠ 2 ∧ Real.logb 2 x = x / 2   := by
  refine ⟨4,by norm_num,by norm_num,?_⟩
  rw [logb_eq_iff_rpow_eq] <;> norm_num
#print axioms solution
