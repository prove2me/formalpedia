-- Prove2me | solution 1 for WorkbookRestored.plus_9408
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:00.128155+00:00
-- url     : https://prove2.me/submissions/be067099-f4d4-4668-b8bc-f34b5907a89c

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_9408.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : x > 0 ∧ x ≠ 1) : x^((Real.log 30) / (Real.log x)) = 30   := by
  rw [← Real.logb_eq_iff_rpow_eq hx.1 hx.2] <;> norm_num [Real.logb]
#print axioms solution
