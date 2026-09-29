-- Prove2me | solution 1 for WorkbookRestored.plus_11374
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:03.355546+00:00
-- url     : https://prove2.me/submissions/a77db9cf-4a3f-4f67-b9af-9dd2137d19d6

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_11374.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x : ℝ, Real.cos x = 1 - 2 * (Real.sin (x / 2))^2   := by
  intro x
  have h := cos_two_mul (x/2)
  have hx : 2*(x/2) = x := by ring
  rw [hx] at h
  nlinarith [sin_sq_add_cos_sq (x/2)]
#print axioms solution
