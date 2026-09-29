-- Prove2me | solution 1 for WorkbookRestored.plus_687
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:17:38.572119+00:00
-- url     : https://prove2.me/submissions/cb32c811-5ac1-4a27-ac50-37c7f574c0cd

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_687.
   Draft repair: only required imports and namespaces are restored. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : x > 0) : Real.exp x > x + 1   := by
  have h1 : 0 < x + 1 := by linarith
  rw [← add_zero (x + 1)]
  have h2 : 0 < 1 + x := by linarith
  simp [exp_pos]
  rw [←log_lt_iff_lt_exp (by positivity)]
  have h3 := log_lt_sub_one_of_pos h1
  nlinarith [h3 (by linarith)]
#print axioms solution
