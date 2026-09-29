-- Prove2me | solution 1 for WorkbookRestored.plus_50350
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:08:44.902698+00:00
-- url     : https://prove2.me/submissions/dfebd4b4-137f-403e-bc2a-075bdc90f2e3

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_50350.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : 1 < x) : Real.log (x * (x ^ 2 + 3) / (3 * x ^ 2 + 1)) < x   := by
  have hx0 : 0 < x := by linarith
  have harg : 0 < x*(x^2+3)/(3*x^2+1) := by positivity
  have hle : x*(x^2+3)/(3*x^2+1) ≤ x := by
    rw [div_le_iff₀ (by positivity : (0:ℝ)<3*x^2+1)]
    nlinarith [mul_nonneg hx0.le (sq_nonneg x)]
  have hl := log_le_log harg hle
  linarith [log_le_sub_one_of_pos hx0]
#print axioms solution
