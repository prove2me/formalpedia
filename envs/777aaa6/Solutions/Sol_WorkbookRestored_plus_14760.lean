-- Prove2me | solution 1 for WorkbookRestored.plus_14760
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:15.436582+00:00
-- url     : https://prove2.me/submissions/8376c107-4526-40d9-9492-0afbd3871349

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_14760.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (u : ℝ) (h : 0 < u) (h' : u ≠ 1) : u - 1 - Real.log u > 0   := by
  have h₁ := log_le_sub_one_of_pos h
  linarith [log_lt_sub_one_of_pos h h']
#print axioms solution
