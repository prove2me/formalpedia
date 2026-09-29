-- Prove2me | solution 1 for WorkbookRestored.plus_39832
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:59.209287+00:00
-- url     : https://prove2.me/submissions/235c5094-5086-4c27-aae4-00e7144d3e4e

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_39832.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x : ℝ, ((sin x)^2 * (cos x)^2) = (sin (2 * x))^2 / 4 ∧ (sin x)^2 = (1 - cos (2 * x)) / 2   := by
  intro x
  constructor
  · rw [sin_two_mul]
    ring
  · rw [cos_two_mul]
    nlinarith [sin_sq_add_cos_sq x]
#print axioms solution
