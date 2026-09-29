-- Prove2me | solution 1 for WorkbookRestored.plus_17727
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:27.750597+00:00
-- url     : https://prove2.me/submissions/ff8f3a71-d592-43d4-9cca-eb3fda17a68a

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_17727.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : Real.sin (36 * π / 180) = Real.cos (54 * π / 180)   := by
  rw [← cos_pi_div_two_sub, ← sub_eq_zero]
  ring_nf
#print axioms solution
