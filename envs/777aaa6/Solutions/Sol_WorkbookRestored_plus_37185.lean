-- Prove2me | solution 1 for WorkbookRestored.plus_37185
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:53.964733+00:00
-- url     : https://prove2.me/submissions/2d5b84f7-4735-406a-93bc-b0bc510aea17

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_37185.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x : ℝ, (Real.sin x)^2 + (Real.sin (2 * x))^2 + (Real.sin (3 * x))^2 + (Real.cos x)^2 + (Real.cos (2 * x))^2 + (Real.cos (3 * x))^2 = 3   := by
  simp [sin_sq, cos_sq, add_assoc, add_comm, add_left_comm]
  exact fun x ↦ by ring
#print axioms solution
