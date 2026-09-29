-- Prove2me | solution 1 for WorkbookRestored.plus_60372
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:05.261934+00:00
-- url     : https://prove2.me/submissions/bded20f3-ebf3-4ba4-ae27-5fdc53ff0e17

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_60372.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x y : ℝ, 2 * sin x * cos y = sin (x + y) + sin (x - y)   := by
  exact fun x y ↦ by rw [sin_add, sin_sub]; ring
#print axioms solution
