-- Prove2me | solution 1 for lean_workbook_plus_12207
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:09:37.401187+00:00
-- url     : https://prove2.me/submissions/6de29652-d6af-4f99-b067-44b0f0dd9bf7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) (hab : a > 0 ∧ b > 0 ∧ a + b = 1) : (1 + 1 / a) * (1 + 1 / b) ≥ 9 := by
  intros
  have p2m_pos_a : (0 : ℝ) < a := by grind
  have p2m_pos_b : (0 : ℝ) < b := by grind
  
  have p2m_cond_2 : (a + b : ℝ) = (1) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (1) - (a + b) = 0 := by linarith only [p2m_cond_2]
  have h_identity : (1 + a + b + ((-8) * a * b)) = (2 : ℝ) * 1 * ((a + ((-1) * b)))^2 := by
    linear_combination ((1 + (2 * a) + (2 * b))) * p2m_cond_2_gap
  have h_nonnegative : (0 : ℝ) ≤ (1 + a + b + ((-8) * a * b)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (a * b) := by positivity
  have h_rational : ((1 + 1 / a) * (1 + 1 / b)) - (9) = ((1 + a + b + ((-8) * a * b))) / ((a * b)) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
