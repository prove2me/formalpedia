-- Prove2me | solution 1 for WorkbookRestored.plus_54693
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:24:54.010246+00:00
-- url     : https://prove2.me/submissions/9625fae6-2cb9-4b2e-a185-f8aed29fec54

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_54693.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution :
  (1 / Real.logb 2 (1 / 7)) + (1 / Real.logb 3 (1 / 7)) + (1 / Real.logb 4 (1 / 7)) + (1 / Real.logb 5 (1 / 7)) + (1 / Real.logb 6 (1 / 7)) - (1 / Real.logb 7 (1 / 7)) - (1 / Real.logb 8 (1 / 7)) - (1 / Real.logb 9 (1 / 7)) - (1 / Real.logb 10 (1 / 7)) = 1   := by
  norm_num [logb, div_eq_mul_inv, inv_inv]
  field_simp [Real.log_ne_zero]
  rw [show (1 : ℝ) / 7 = 2 * 3 * 4 * 5 * 6 / (7 * 8 * 9 * 10) by norm_num]
  simp [Real.log_mul, Real.log_div, mul_comm, mul_assoc, mul_left_comm]
  ring
#print axioms solution
