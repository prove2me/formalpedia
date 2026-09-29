-- Prove2me | solution 1 for WorkbookRestored.plus_8018
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:31:13.778801+00:00
-- url     : https://prove2.me/submissions/de8db2bc-99db-4bb4-989f-e32dfe9ec392

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_8018.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : 0 < x) : (Real.log x) / (x + 1) ≤ (Real.log (x + 1)) / x   := by
  gcongr
  exacts [log_nonneg (by linarith), by linarith, by linarith]
#print axioms solution
