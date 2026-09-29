-- Prove2me | solution 1 for WorkbookRestored.plus_16723
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:24.671531+00:00
-- url     : https://prove2.me/submissions/cc99ac50-11fd-4db3-b01a-2c06eb307441

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_16723.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (k : ℝ) (h₁ : 0 < k) (h₂ : k < Real.pi / 2) : 1 / Real.sin k > 1   := by
  rw [div_eq_mul_inv]
  simp [h₁, h₂]
  rw [← one_div]
  rw [← sin_pi_div_two]
  rw [lt_div_iff₀ (sin_pos_of_pos_of_lt_pi h₁ (by linarith))]
  rw [sin_pi_div_two, one_mul]
  rw [← sin_pi_div_two]
  exact sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) h₂
#print axioms solution
