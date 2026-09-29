-- Prove2me | solution 1 for lean_workbook_plus_22613
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:05:21.953163+00:00
-- url     : https://prove2.me/submissions/8e310c13-d234-4f5b-84eb-36be49c09f95

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (habc : a * b * c = 1) : a + b + c ≥ 2 / (a + 1) + 2 / (b + 1) + 2 / (c + 1) := by
  intros
  have p2m_cond_0 : (0 : ℝ) ≤ (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) ≤ (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (0 : ℝ) ≤ (c) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (c) - (0) := by linarith only [p2m_cond_2]
  have p2m_cond_3 : (a * b * c : ℝ) = (1) := by first | assumption | aesop | linarith
  have p2m_cond_3_gap : (1) - (a * b * c) = 0 := by linarith only [p2m_cond_3]
  have h_identity : ((-6) + (a ^ 2) + (b ^ 2) + (c ^ 2) + ((-3) * a) + ((-3) * b) + ((-3) * c) + (a * (b ^ 2)) + (a * (c ^ 2)) + (b * (a ^ 2)) + (b * (c ^ 2)) + (c * (a ^ 2)) + (c * (b ^ 2)) + (a * b * (c ^ 2)) + (a * c * (b ^ 2)) + (b * c * (a ^ 2)) + (3 * a * b * c)) = (1 : ℝ) * 1 * ((1 + ((-1) * a)))^2 + (1 : ℝ) * 1 * ((1 + ((-1) * b)))^2 + (1 : ℝ) * 1 * ((1 + ((-1) * c)))^2 + (1 : ℝ) * ((a) - (0)) * ((b + ((-1) * c)))^2 + (1 : ℝ) * ((b) - (0)) * ((a + ((-1) * c)))^2 + (1 : ℝ) * ((c) - (0)) * ((a + ((-1) * b)))^2 := by
    linear_combination (((-9) + ((-1) * a) + ((-1) * b) + ((-1) * c))) * p2m_cond_3_gap
  have h_nonnegative : (0 : ℝ) ≤ ((-6) + (a ^ 2) + (b ^ 2) + (c ^ 2) + ((-3) * a) + ((-3) * b) + ((-3) * c) + (a * (b ^ 2)) + (a * (c ^ 2)) + (b * (a ^ 2)) + (b * (c ^ 2)) + (c * (a ^ 2)) + (c * (b ^ 2)) + (a * b * (c ^ 2)) + (a * c * (b ^ 2)) + (b * c * (a ^ 2)) + (3 * a * b * c)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((1 + a) * (1 + b) * (1 + c)) := by positivity
  have h_rational : (a + b + c) - (2 / (a + 1) + 2 / (b + 1) + 2 / (c + 1)) = (((-6) + (a ^ 2) + (b ^ 2) + (c ^ 2) + ((-3) * a) + ((-3) * b) + ((-3) * c) + (a * (b ^ 2)) + (a * (c ^ 2)) + (b * (a ^ 2)) + (b * (c ^ 2)) + (c * (a ^ 2)) + (c * (b ^ 2)) + (a * b * (c ^ 2)) + (a * c * (b ^ 2)) + (b * c * (a ^ 2)) + (3 * a * b * c))) / (((1 + a) * (1 + b) * (1 + c))) := by
    field_simp (disch := positivity)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
