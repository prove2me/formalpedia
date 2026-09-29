-- Prove2me | solution 1 for WorkbookRestored.plus_4774
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:31:05.272724+00:00
-- url     : https://prove2.me/submissions/cb369509-4f2c-491e-a123-0928df15f0f0

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_4774.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ b c : ℝ, ∀ α : ℝ, (α ≠ 0 ∧ α ≠ π) → 16 * (1 / 2 * b * c * Real.sin α) ^ 2 = 4 * b ^ 2 * c ^ 2 * (Real.sin α) ^ 2   := by
  intro b c α hα
  ring
#print axioms solution
