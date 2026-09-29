-- Prove2me | solution 1 for lean_workbook_plus_4208
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:08:01.620455+00:00
-- url     : https://prove2.me/submissions/0eeb86fc-31ea-4dd5-9b9e-e5dd2dc5507c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b + 1 = 3 * a * b) : 1 / (a * (b + 1)) + 1 / (b * (a + 1)) ≤ 1 := by
  intros
  have p2m_cond_2 : (a + b + 1 : ℝ) = (3 * a * b) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (3 * a * b) - (a + b + 1) = 0 := by linarith only [p2m_cond_2]
  have h_identity : (((-1) * a) + ((-1) * b) + (a * (b ^ 2)) + (b * (a ^ 2)) + ((a ^ 2) * (b ^ 2)) + ((-1) * a * b)) = ((5 / 36) : ℝ) * 1 * ((1 + ((-1) * a)))^2 + ((5 / 36) : ℝ) * 1 * ((1 + ((-1) * b)))^2 + ((11 / 36) : ℝ) * 1 * ((a + ((-1) * b)))^2 := by
    linear_combination (((5 / 18) + ((4 / 9) * a) + ((4 / 9) * b) + ((1 / 3) * a * b))) * p2m_cond_2_gap
  have h_nonnegative : (0 : ℝ) ≤ (((-1) * a) + ((-1) * b) + (a * (b ^ 2)) + (b * (a ^ 2)) + ((a ^ 2) * (b ^ 2)) + ((-1) * a * b)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (a * b * (1 + a) * (1 + b)) := by positivity
  have h_rational : (1) - (1 / (a * (b + 1)) + 1 / (b * (a + 1))) = ((((-1) * a) + ((-1) * b) + (a * (b ^ 2)) + (b * (a ^ 2)) + ((a ^ 2) * (b ^ 2)) + ((-1) * a * b))) / ((a * b * (1 + a) * (1 + b))) := by
    field_simp (disch := positivity)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
