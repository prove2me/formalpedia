-- Prove2me | solution 1 for WorkbookRestored.plus_54169
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:24:51.753976+00:00
-- url     : https://prove2.me/submissions/0e421657-f732-45f9-a858-214ce6d8f918

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_54169.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : 0 < x) : (1 + Real.log x) * Real.log x + 1 / x > 0   := by
  rw [add_comm]
  rw [add_mul, one_mul]
  rw [← sub_neg_eq_add]
  simp [sub_pos, mul_add, add_mul, mul_comm, mul_left_comm]
  have : 0 < x⁻¹ := inv_pos.mpr hx
  have := log_le_sub_one_of_pos this
  nlinarith [log_inv x]
#print axioms solution
