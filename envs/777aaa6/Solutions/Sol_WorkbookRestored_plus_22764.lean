-- Prove2me | solution 1 for WorkbookRestored.plus_22764
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:43.934293+00:00
-- url     : https://prove2.me/submissions/9c8e613b-5fd9-4753-8b07-63c277a78020

/- Adapted from internlm/Lean-Workbook, Apache-2.0; row lean_workbook_plus_22764.
   Only missing imports/namespaces and the declaration name are repaired. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : x < 0) :
  Real.exp (-x) > -2 * x / (x ^ 2 + 1)   := by
  have hd : 0 < x^2+1 := by positivity
  rw [gt_iff_lt, div_lt_iff₀ hd]
  have he : 1 < Real.exp (-x) := Real.one_lt_exp_iff.mpr (neg_pos.mpr hx)
  have hp := mul_lt_mul_of_pos_right he hd
  nlinarith [sq_nonneg (x+1)]
#print axioms solution
