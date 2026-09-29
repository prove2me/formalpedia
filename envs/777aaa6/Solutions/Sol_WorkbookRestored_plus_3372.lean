-- Prove2me | solution 1 for WorkbookRestored.plus_3372
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:29:22.206979+00:00
-- url     : https://prove2.me/submissions/a57ea9b5-6f6a-4eaf-bd28-9d9729eb4bbc

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_3372.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : 0 < x) : 1 + 2 * Real.log x ≤ x^2   := by
  nlinarith [add_sq (Real.log x) 1, log_le_sub_one_of_pos hx]
#print axioms solution
