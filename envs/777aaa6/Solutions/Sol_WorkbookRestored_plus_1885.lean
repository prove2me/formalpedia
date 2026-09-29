-- Prove2me | solution 1 for WorkbookRestored.plus_1885
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:17:44.911981+00:00
-- url     : https://prove2.me/submissions/abba9ac3-b0b2-42e6-966a-9e10b7b341ca

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_1885.
   Draft repair: only required imports and namespaces are restored. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (A B C : ℝ) (hA : 0 < A ∧ A <= π ∧ B <= π ∧ C <= π ∧ A + B + C = π) : Real.sin (2 * A) + Real.sin (2 * B) + Real.sin (2 * C) = 4 * Real.sin A * Real.sin B * Real.sin C   := by
  have hC : C = π - (A+B) := by linarith [hA.2.2.2.2]
  rw [hC]
  simp only [sin_two_mul, sin_pi_sub, cos_pi_sub, sin_add, cos_add]
  linear_combination -2 * (sin A * cos A) * (sin_sq_add_cos_sq B) - 2 * (sin B * cos B) * (sin_sq_add_cos_sq A)
#print axioms solution
