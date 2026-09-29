-- Prove2me | solution 1 for WorkbookRestored.plus_8656
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:34:55.181975+00:00
-- url     : https://prove2.me/submissions/06d2e2bb-8f7d-439d-82c6-58e9cd72dfdb

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_8656.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : 0 ≤ x) : exp x ≥ x + 1   := by
  nlinarith [add_one_le_exp x]
#print axioms solution
