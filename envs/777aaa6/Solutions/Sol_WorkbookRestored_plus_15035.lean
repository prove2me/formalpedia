-- Prove2me | solution 1 for WorkbookRestored.plus_15035
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:16.823244+00:00
-- url     : https://prove2.me/submissions/8f08030e-464b-4510-9b50-8e1e4efa89e1

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_15035.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (θ : ℝ) (h : 2 * sin θ ^ 2 = 5/7) : sin (2 * θ) ^ 2 = 45/49   := by
  rw [show (2 : ℝ) * θ = (2 : ℝ) * θ by rfl, Real.sin_two_mul]
  nlinarith [sin_sq_add_cos_sq θ]
#print axioms solution
