-- Prove2me | solution 1 for WorkbookRestored.plus_14676
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:13.882451+00:00
-- url     : https://prove2.me/submissions/fb6633fd-2bf6-4df7-a468-482f0d881947

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_14676.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x y z : ℝ, sin (x + y) * sin (y + z) = sin y * sin (x + y + z) + sin z * sin x   := by
  intro x y z
  simp [sin_add, sin_add, cos_add, cos_add, cos_add, cos_add, cos_add, cos_add, cos_add, cos_add]
  ring
  simp [sin_sq, sin_sq, sin_sq, sin_sq, sin_sq, sin_sq, sin_sq, sin_sq, sin_sq, sin_sq]
  ring
#print axioms solution
