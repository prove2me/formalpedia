-- Prove2me | solution 1 for lean_workbook_plus_20208
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:06:01.98455+00:00
-- url     : https://prove2.me/submissions/c304ab6c-de54-414c-847c-432f8bb5ce1f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 2) : 1 / (11 + a^2) + 1 / (11 + b^2) ≤ 1 / 6 := by
  intros
  have p2m_cond_2 : (a + b : ℝ) = (2) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (2) - (a + b) = 0 := by linarith only [p2m_cond_2]
  have h_identity : ((-11) + (5 * (a ^ 2)) + (5 * (b ^ 2)) + ((a ^ 2) * (b ^ 2))) = ((1 / 2) : ℝ) * 1 * ((a + ((-1) * a * b)))^2 + ((7 / 4) : ℝ) * 1 * ((a + ((-1) * b)))^2 + ((1 / 2) : ℝ) * 1 * ((((-1) * b) + (a * b)))^2 := by
    linear_combination (((-11 / 2) + ((-11 / 4) * a) + ((-11 / 4) * b) + ((-1) * a * b))) * p2m_cond_2_gap
  have h_nonnegative : (0 : ℝ) ≤ ((-11) + (5 * (a ^ 2)) + (5 * (b ^ 2)) + ((a ^ 2) * (b ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (6 * (11 + (a ^ 2)) * (11 + (b ^ 2))) := by positivity
  have h_rational : (1 / 6) - (1 / (11 + a^2) + 1 / (11 + b^2)) = (((-11) + (5 * (a ^ 2)) + (5 * (b ^ 2)) + ((a ^ 2) * (b ^ 2)))) / ((6 * (11 + (a ^ 2)) * (11 + (b ^ 2)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
