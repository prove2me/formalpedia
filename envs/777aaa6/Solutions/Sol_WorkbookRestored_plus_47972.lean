-- Prove2me | solution 1 for WorkbookRestored.plus_47972
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:05:13.69577+00:00
-- url     : https://prove2.me/submissions/39c08b76-0e67-4387-96e5-e8d472f78c99

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_47972.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (A B C : ℝ) (hx: A > 0 ∧ B > 0 ∧ C > 0) (hab : A + B + C = π) : 4 * Real.cos (A / 2) * Real.cos (B / 2) * Real.cos (C / 2) ≥ Real.sin (A + B + C)   := by
  simp [hx.1, hx.2.1, hx.2.2, hab]
  exact mul_nonneg (mul_nonneg (mul_nonneg zero_le_four (cos_nonneg_of_mem_Icc ⟨by linarith [hx.1], by linarith [hx.1]⟩)) (cos_nonneg_of_mem_Icc ⟨by linarith [hx.2.1], by linarith [hx.2.1]⟩)) (cos_nonneg_of_mem_Icc ⟨by linarith [hx.2.2], by linarith [hx.2.2]⟩)
#print axioms solution
