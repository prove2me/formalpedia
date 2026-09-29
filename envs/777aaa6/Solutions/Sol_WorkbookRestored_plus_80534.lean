-- Prove2me | solution 1 for WorkbookRestored.plus_80534
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:34.277123+00:00
-- url     : https://prove2.me/submissions/a95a02a5-1ca0-454c-b110-6d0d7ae86f57

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_80534.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx_pos : 0 < x) (hx_lt_one : x < 1) : exp x < 1 / (1 - x)   := by
  have hx_0_lt_1 : 0 < 1 - x := by linarith
  nlinarith [Real.exp_bound_div_one_sub_of_interval' hx_pos hx_lt_one]
#print axioms solution
