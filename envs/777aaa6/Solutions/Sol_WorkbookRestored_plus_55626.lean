-- Prove2me | solution 1 for WorkbookRestored.plus_55626
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:24:54.857806+00:00
-- url     : https://prove2.me/submissions/c0ebd48e-e706-4b9f-a8f7-b3dcf4dcb7d1

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_55626.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x : ℝ, ((sin x ^ 2 + cos x ^ 2) ^ 2 - 2 * sin x ^ 2 * cos x ^ 2) / (sin x * cos x) = (2 - sin (2 * x) ^ 2) / sin (2 * x)   := by
  intro x
  rw [sin_sq_add_cos_sq,sin_two_mul]
  ring
#print axioms solution
