-- Prove2me | solution 1 for WorkbookRestored.plus_32073
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:36.806261+00:00
-- url     : https://prove2.me/submissions/0b95af42-f5ee-4ebb-9fd4-18577fde6a28

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_32073.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) : (cos x)^4 = 1 / 8 * cos (4 * x) + 1 / 2 * cos (2 * x) + 3 / 8   := by
  rw [show (4 : ℝ) * x = 2 * (2 * x) by ring, cos_two_mul]
  nlinarith [cos_two_mul x, sin_two_mul x]
#print axioms solution
