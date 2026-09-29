-- Prove2me | solution 1 for WorkbookRestored.plus_41922
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:05:04.714866+00:00
-- url     : https://prove2.me/submissions/5b461307-3576-4d3e-ae8c-64c22abde572

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_41922.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x : ℝ, (cos x)^3 - (cos x)^2 = (cos x)^2 * (cos x - 1) ∧ (cos x)^2 * (cos x - 1) ≤ 0   := by
  exact fun x ↦ ⟨by ring, mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (cos x)) (by linarith [cos_le_one x])⟩
#print axioms solution
