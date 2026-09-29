-- Prove2me | solution 1 for WorkbookRestored.plus_2535
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:29:19.054852+00:00
-- url     : https://prove2.me/submissions/edefd90f-e2ff-4fc0-bacf-719f389e3127

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_2535.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x : ℝ, Real.cos (2 * x) = 2 * (Real.cos x)^2 - 1   := by
  exact fun x ↦ Real.cos_two_mul x
#print axioms solution
