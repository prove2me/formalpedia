-- Prove2me | solution 1 for WorkbookRestored.plus_5722
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:31:09.161492+00:00
-- url     : https://prove2.me/submissions/643b953e-cd64-4a5b-ac61-61658644266c

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_5722.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a b : ℝ) : 2 * cos a * cos b = cos (a + b) + cos (a - b)   := by
  simp [cos_add, cos_sub, mul_add, mul_sub, mul_comm, mul_left_comm]
  ring
#print axioms solution
