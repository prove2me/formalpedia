-- Prove2me | solution 1 for lean_workbook_plus_6933
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:08:23.623883+00:00
-- url     : https://prove2.me/submissions/7c60def2-3efe-4df2-9566-0099adc8f060

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution : ∀ c d : ℝ, c > 0 ∧ d > 0 → c^2 / d + d ≥ 2 * c := by
  intro c d
  intros
  have hc0 : 0 < c := by aesop
  have hd0 : 0 < d := by aesop
  
  have h_identity : ((c ^ 2) + (d ^ 2) + ((-2) * c * d)) = (1 : ℝ) * 1 * ((c + ((-1) * d)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((c ^ 2) + (d ^ 2) + ((-2) * c * d)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < d := by first | positivity | nlinarith | aesop
  have h_rational : (c^2 / d + d) - (2 * c) = (((c ^ 2) + (d ^ 2) + ((-2) * c * d))) / (d) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
