-- Prove2me | solution 1 for WorkbookRestored.plus_11509
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:04.279334+00:00
-- url     : https://prove2.me/submissions/45dba5ab-be80-42b6-b8ca-1dbeb3b3bec8

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_11509.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx: x > 0) : Real.log (x^3 - 2 * x^2 + x + 1) ≥ 0   := by
  refine' Real.log_nonneg (by nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 1 / 2)])
#print axioms solution
