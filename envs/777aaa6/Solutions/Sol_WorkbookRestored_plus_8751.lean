-- Prove2me | solution 1 for WorkbookRestored.plus_8751
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:34:56.965482+00:00
-- url     : https://prove2.me/submissions/97e47875-252a-4ffc-93e2-9c9eb088d679

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_8751.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (θ : ℝ) : (sin θ)^2 + (cos θ)^2 = 1   := by
  simp [sin_sq, cos_sq, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
#print axioms solution
