-- Prove2me | solution 1 for WorkbookRestored.plus_68127
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:17.327901+00:00
-- url     : https://prove2.me/submissions/cdbacccd-1da3-4011-a41a-dcb2134cf9b9

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_68127.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x : ℝ, Real.log (1 + Real.exp x) = x + Real.log (1 + Real.exp (-x))   := by
  intro x
  have he : 1+exp x = exp x * (1+exp (-x)) := by rw [exp_neg];field_simp;ring
  rw [he,log_mul (exp_ne_zero x) (ne_of_gt (by positivity : (0:ℝ)<1+exp (-x))),log_exp]
#print axioms solution
