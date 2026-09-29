-- Prove2me | solution 1 for WorkbookRestored.plus_51489
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:08:48.982537+00:00
-- url     : https://prove2.me/submissions/06cd0fdb-9311-4abb-95de-f30751040d21

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_51489.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a : ℝ) (ha : 1 < a) : 1 - (1 / a) - Real.log a < 0   := by
  rw [sub_neg]
  have h : 0 < 1 / a := one_div_pos.mpr (zero_lt_one.trans ha)
  rw [← neg_lt_neg_iff, ← log_inv, inv_eq_one_div]
  have := log_lt_sub_one_of_pos h
  simpa using this (by simpa using ha.ne')
#print axioms solution
