-- Prove2me | solution 1 for WorkbookRestored.plus_32385
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:38.948264+00:00
-- url     : https://prove2.me/submissions/90125819-2928-4a22-98f7-5413f6af30c8

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_32385.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x : ℝ, sin x ^ 4 - cos x ^ 4 = -cos (2 * x)   := by
  intro x
  simp [sq, sin_two_mul, cos_two_mul]
  nlinarith [sin_sq_add_cos_sq x]
#print axioms solution
