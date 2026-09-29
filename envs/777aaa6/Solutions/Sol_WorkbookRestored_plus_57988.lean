-- Prove2me | solution 1 for WorkbookRestored.plus_57988
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:00.33261+00:00
-- url     : https://prove2.me/submissions/60a72f80-1011-4d7c-a5fd-46820cadba1a

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_57988.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n : ℤ) : 24 * (cos (n * π / 9))^4 ≤ 9 * (cos (n * π / 9))^2 + 16 * (cos (n * π / 9))^6   := by
  simp [sq, mul_add, mul_comm, mul_left_comm]
  nlinarith [sq_nonneg (3 * cos (π * n / 9) - 4 * cos (π * n / 9) ^ 3)]
#print axioms solution
