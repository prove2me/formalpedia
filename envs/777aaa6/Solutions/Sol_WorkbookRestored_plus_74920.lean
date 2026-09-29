-- Prove2me | solution 1 for WorkbookRestored.plus_74920
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:26.119073+00:00
-- url     : https://prove2.me/submissions/84c19a32-77df-4490-b03d-5100f895dccc

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_74920.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : 1 < x) : x^2 * (Real.exp (-x^9)) < x^2 * (Real.exp (-x^3))   := by
  have hp : x^3 < x^9 := pow_lt_pow_right₀ hx (by norm_num)
  exact mul_lt_mul_of_pos_left (exp_lt_exp.2 (neg_lt_neg hp)) (sq_pos_of_pos (zero_lt_one.trans hx))
#print axioms solution
