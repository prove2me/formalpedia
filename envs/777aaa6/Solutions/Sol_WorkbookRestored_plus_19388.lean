-- Prove2me | solution 1 for WorkbookRestored.plus_19388
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:34.100106+00:00
-- url     : https://prove2.me/submissions/2adad648-2719-4b41-a172-abc832f0c72c

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_19388.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x : ℝ, sin (-x) = -sin x   := by
  exact fun x ↦ by simp [sin, exp_neg, (neg_div _ _).symm, add_mul, mul_add, mul_comm, mul_left_comm]
#print axioms solution
