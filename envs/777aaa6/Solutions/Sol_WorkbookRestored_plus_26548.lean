-- Prove2me | solution 1 for WorkbookRestored.plus_26548
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:01:53.559514+00:00
-- url     : https://prove2.me/submissions/6650b62c-0b80-4176-9a2c-2dd99d70ca2a

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_26548.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n : ℕ) (hn : 1 ≤ n) : Real.log (n + 1) < n   := by
  have := log_lt_sub_one_of_pos (Nat.cast_add_one_pos n)
  simpa using this (by norm_cast; linarith)
#print axioms solution
