-- Prove2me | solution 1 for WorkbookRestored.plus_34337
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:48.129898+00:00
-- url     : https://prove2.me/submissions/7696f881-1be6-4f73-a617-788a15304ebc

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_34337.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : 1 ≤ x) : 1 - 1 / x ≤ Real.log x ∧ Real.log x < 1 + x   := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hlo := log_le_sub_one_of_pos (inv_pos.mpr hxpos)
  rw [log_inv] at hlo
  have hhi := log_le_sub_one_of_pos hxpos
  simp only [one_div]
  constructor <;> linarith
#print axioms solution
