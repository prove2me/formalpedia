-- Prove2me | solution 1 for lean_workbook_plus_5508
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:39:23.20404+00:00
-- url     : https://prove2.me/submissions/8b83af6d-e01d-425c-9362-4066dc1ab35a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b = 1) : 1 / a + 1 / b + 4 / (a + b) ≥ 4 := by
  intros
  have p2m_cond_2 : (a * b : ℝ) = (1) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (1) - (a * b) = 0 := by linarith only [p2m_cond_2]
  have h_identity : ((a ^ 2) + (b ^ 2) + ((-4) * a * (b ^ 2)) + ((-4) * b * (a ^ 2)) + (6 * a * b)) = (4 : ℝ) * 1 * ((1 + ((-1 / 2) * a) + ((-1 / 2) * b)))^2 := by
    linear_combination (((-4) + (4 * a) + (4 * b))) * p2m_cond_2_gap
  have h_nonnegative : (0 : ℝ) ≤ ((a ^ 2) + (b ^ 2) + ((-4) * a * (b ^ 2)) + ((-4) * b * (a ^ 2)) + (6 * a * b)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (a * b * (a + b)) := by positivity
  have h_rational : (1 / a + 1 / b + 4 / (a + b)) - (4) = (((a ^ 2) + (b ^ 2) + ((-4) * a * (b ^ 2)) + ((-4) * b * (a ^ 2)) + (6 * a * b))) / ((a * b * (a + b))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
