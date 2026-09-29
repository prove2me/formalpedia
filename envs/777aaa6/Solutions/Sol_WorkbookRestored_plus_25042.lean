-- Prove2me | solution 1 for WorkbookRestored.plus_25042
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:01:46.501984+00:00
-- url     : https://prove2.me/submissions/82509ebf-a848-430f-86a6-e1869a08cf1e

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_25042.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution :
  Real.logb 2 (Real.logb 4 16) = 1   := by
  rw [show (16 : ℝ) = 4 ^ (2 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]
  rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
#print axioms solution
