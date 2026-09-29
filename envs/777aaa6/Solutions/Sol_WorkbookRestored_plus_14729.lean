-- Prove2me | solution 1 for WorkbookRestored.plus_14729
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:14.596006+00:00
-- url     : https://prove2.me/submissions/fa226fa0-425b-4e59-9603-846570a017e4

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_14729.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ A : ℝ, (9 / 4 - 4 * (Real.sin (A / 2) - 1 / 4) ^ 2) ≤ 9 / 4   := by
  exact fun A ↦ by nlinarith [sq_nonneg (sin (A / 2) - 1 / 4)]
#print axioms solution
