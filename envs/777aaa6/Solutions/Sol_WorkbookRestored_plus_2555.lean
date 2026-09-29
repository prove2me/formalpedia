-- Prove2me | solution 1 for WorkbookRestored.plus_2555
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:29:19.756482+00:00
-- url     : https://prove2.me/submissions/1d3e214e-b8ba-4ec1-9595-0cf41fd6dc72

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_2555.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (α β γ : ℝ) :
  sin α * sin β * sin γ * sin (α + β + γ) =
  sin α * sin γ * sin (α + β) * sin (β + γ) -
  sin α ^ 2 * sin γ ^ 2   := by
  simp [sin_add, cos_add, sin_sub, cos_sub]
  ring
  simp [sin_sq, cos_sq]
  ring
#print axioms solution
