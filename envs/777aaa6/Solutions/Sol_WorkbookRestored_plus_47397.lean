-- Prove2me | solution 1 for WorkbookRestored.plus_47397
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:08:41.213582+00:00
-- url     : https://prove2.me/submissions/5d485b50-727e-4b96-a3b0-50fa3a0cd0f1

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_47397.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution :  ∀ x : ℝ, (sin x * (1 - cos x) / (1 - cos x ^ 2) - sin x * (1 + cos x) / (1 - cos x ^ 2) = -2 * cos x * sin x / sin x ^ 2)   := by
  intro x
  have hs : 1-cos x^2 = sin x^2 := by nlinarith [sin_sq_add_cos_sq x]
  rw [hs]
  ring
#print axioms solution
