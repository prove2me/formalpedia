-- Prove2me | solution 1 for WorkbookRestored.plus_59884
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:01.938438+00:00
-- url     : https://prove2.me/submissions/96798c2f-35f6-43c3-8996-cbd67493ac98

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_59884.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x : ℝ, sin x ^ 6 + cos x ^ 6 - 1 = -3 * sin x ^ 2 * cos x ^ 2   := by
  intro x
  have := sq_nonneg (sin x ^ 2 - cos x ^ 2)
  rw [sub_sq] at this
  nlinarith [sin_sq_add_cos_sq x]
#print axioms solution
