-- Prove2me | solution 1 for WorkbookRestored.plus_31177
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:34.725701+00:00
-- url     : https://prove2.me/submissions/a6ffe10f-18d1-4053-8d49-88ada215c58b

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_31177.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ π) (hy : 0 ≤ y ∧ y ≤ π) :
  sin ((x + y) / 2) * cos ((x - y) / 2) ≤ sin ((x + y) / 2)   := by
  apply mul_le_of_le_one_right (sin_nonneg_of_nonneg_of_le_pi _ _)
  exacts [cos_le_one _, by linarith, by linarith]
#print axioms solution
