-- Prove2me | solution 1 for WorkbookRestored.plus_7240
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:31:12.181157+00:00
-- url     : https://prove2.me/submissions/396bde60-b551-43db-912a-ba781b5e5177

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_7240.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x y : ℝ, sin x * sin y = 1 / 2 * (cos (x - y) - cos (x + y))   := by
  exact fun x y ↦ by rw [cos_add, cos_sub]; ring
#print axioms solution
