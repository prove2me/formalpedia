-- Prove2me | solution 1 for WorkbookRestored.plus_12106
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:07.73096+00:00
-- url     : https://prove2.me/submissions/6cba996b-56f9-4de8-aca8-fa0b94ef051c

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_12106.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a b : ℝ) : sin a * cos a + sin b * cos b = sin (a + b) * cos (a - b)   := by
  simp [sin_add, sin_sub, cos_add, cos_sub, mul_add, mul_sub, mul_comm, mul_left_comm]
  ring
  simp [cos_sq', sin_sq_add_cos_sq]
  ring
#print axioms solution
