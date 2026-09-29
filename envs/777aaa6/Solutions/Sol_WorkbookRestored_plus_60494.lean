-- Prove2me | solution 1 for WorkbookRestored.plus_60494
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:06.946981+00:00
-- url     : https://prove2.me/submissions/4977980f-5b2b-41c2-8af3-8bd9c857687a

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_60494.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a : ℝ) (ha : 0 < a ∧ a < Real.pi / 4) : Real.log (Real.tan (Real.pi / 4 - a)) = -Real.log (Real.tan (Real.pi / 4 + a))   := by
  simp [ha.1, ha.2, tan_eq_sin_div_cos, sin_pi_div_four, cos_pi_div_four, add_comm]
  rw [← Real.log_inv]
  simp [add_comm, sub_eq_add_neg, sin_add, cos_add, sin_pi_div_four, cos_pi_div_four]
#print axioms solution
