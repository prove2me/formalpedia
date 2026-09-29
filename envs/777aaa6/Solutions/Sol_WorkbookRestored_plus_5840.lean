-- Prove2me | solution 1 for WorkbookRestored.plus_5840
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:31:09.892693+00:00
-- url     : https://prove2.me/submissions/08f28982-e382-4cb2-9f95-d7e9be90972f

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_5840.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : x < 1) : x + Real.log (1 - x) ≤ 0   := by
  nlinarith [log_le_sub_one_of_pos (sub_pos_of_lt hx)]
#print axioms solution
