-- Prove2me | solution 1 for lean_workbook_plus_13156
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:05:22.26643+00:00
-- url     : https://prove2.me/submissions/e022c6db-98a3-4b7f-a68d-b9cc5e4618d8

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a^2 + b^2 = 1) (hcd : c^2 + d^2 = 1) : b / a + d / c ≥ 2 * (b + d) / (a + c) := by
  intros
  have p2m_cond_1 : (0 : ℝ) < (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_3 : (0 : ℝ) < (d) := by first | assumption | aesop | linarith
  have p2m_cond_3_gap : (0 : ℝ) ≤ (d) - (0) := by linarith only [p2m_cond_3]
  have p2m_cond_4 : (a^2 + b^2 : ℝ) = (1) := by first | assumption | aesop | linarith
  have p2m_cond_4_gap : (1) - (a^2 + b^2) = 0 := by linarith only [p2m_cond_4]
  have p2m_cond_5 : (c^2 + d^2 : ℝ) = (1) := by first | assumption | aesop | linarith
  have p2m_cond_5_gap : (1) - (c^2 + d^2) = 0 := by linarith only [p2m_cond_5]
  have h_identity : ((b * (c ^ 2)) + (d * (a ^ 2)) + ((-1) * a * b * c) + ((-1) * a * c * d)) = ((1 / 2) : ℝ) * ((b) - (0)) * ((a + ((-1) * c)))^2 + ((1 / 2) : ℝ) * ((b) - (0)) * ((b + ((-1) * d)))^2 + ((1 / 2) : ℝ) * ((d) - (0)) * ((a + ((-1) * c)))^2 + ((1 / 2) : ℝ) * ((d) - (0)) * ((b + ((-1) * d)))^2 := by
    linear_combination ((((1 / 2) * b) + ((-1 / 2) * d))) * p2m_cond_4_gap + ((((1 / 2) * d) + ((-1 / 2) * b))) * p2m_cond_5_gap
  have h_nonnegative : (0 : ℝ) ≤ ((b * (c ^ 2)) + (d * (a ^ 2)) + ((-1) * a * b * c) + ((-1) * a * c * d)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (a * c * (a + c)) := by positivity
  have h_rational : (b / a + d / c) - (2 * (b + d) / (a + c)) = (((b * (c ^ 2)) + (d * (a ^ 2)) + ((-1) * a * b * c) + ((-1) * a * c * d))) / ((a * c * (a + c))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
