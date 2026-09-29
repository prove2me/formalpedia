-- Prove2me | solution 1 for WorkbookRestored.plus_26636
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:01:54.243988+00:00
-- url     : https://prove2.me/submissions/de93789c-6bb6-4b59-850f-398d4d2a874d

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_26636.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : 0 < x) : Real.log x ≤ x - 1   := by
  nlinarith [log_le_sub_one_of_pos hx]
#print axioms solution
