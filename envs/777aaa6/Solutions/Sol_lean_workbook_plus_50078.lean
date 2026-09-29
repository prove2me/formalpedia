-- Prove2me | solution 1 for lean_workbook_plus_50078
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:15:01.433536+00:00
-- url     : https://prove2.me/submissions/1d885d78-1914-4346-9142-cfbfafdba487

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (h1 : a ≥ b ∧ b ≥ c) (h2 : 0 < a ∧ 0 < b ∧ 0 < c) (h3 : a * b * c = 1) : a / (b + a) + c / (a + c) + b / (b + c) ≤ 2 := by
  intros
  have p2m_cond_0 : (b : ℝ) ≤ (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (b) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (c : ℝ) ≤ (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (c) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (0 : ℝ) < (a) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_2]
  have p2m_cond_3 : (0 : ℝ) < (b) := by first | assumption | aesop | linarith
  have p2m_cond_3_gap : (0 : ℝ) ≤ (b) - (0) := by linarith only [p2m_cond_3]
  have p2m_cond_4 : (0 : ℝ) < (c) := by first | assumption | aesop | linarith
  have p2m_cond_4_gap : (0 : ℝ) ≤ (c) - (0) := by linarith only [p2m_cond_4]
  have p2m_cond_5 : (a * b * c : ℝ) = (1) := by first | assumption | aesop | linarith
  have p2m_cond_5_gap : (1) - (a * b * c) = 0 := by linarith only [p2m_cond_5]
  have h_identity : ((a * (b ^ 2)) + (b * (c ^ 2)) + (c * (a ^ 2)) + (a * b * c)) = ((142 / 4895) : ℝ) * 1 * ((1 + ((-2) * b)))^2 + ((213 / 4895) : ℝ) * 1 * ((1 + ((-2) * c)))^2 + ((863 / 3916) : ℝ) * ((a) - (b)) * (b)^2 + ((213 / 4895) : ℝ) * ((b) - (c)) * ((1 + (2 * c)))^2 + ((287 / 4895) : ℝ) * ((b) - (c)) * ((b + ((-2) * c)))^2 + ((1453 / 3916) : ℝ) * ((a) - (0)) * (b)^2 + ((400 / 979) : ℝ) * ((a) - (0)) * ((b + c))^2 + ((142 / 4895) : ℝ) * ((b) - (0)) * ((1 + ((-2) * b)))^2 + ((213 / 4895) : ℝ) * ((b) - (0)) * ((1 + ((-2) * c)))^2 + ((179 / 3916) : ℝ) * ((b) - (0)) * ((b + (2 * c)))^2 + ((213 / 1958) : ℝ) * ((c) - (0)) * ((1 + (2 * a)))^2 + ((213 / 1958) : ℝ) * ((c) - (0)) * ((1 + ((-2) * a)))^2 + ((27 / 979) : ℝ) * ((c) - (0)) * ((a + (2 * b)))^2 + ((100 / 979) : ℝ) * ((c) - (0)) * ((a + ((-2) * c)))^2 := by
    linear_combination ((-71 / 979)) * p2m_cond_5_gap
  have h_nonnegative : (0 : ℝ) ≤ ((a * (b ^ 2)) + (b * (c ^ 2)) + (c * (a ^ 2)) + (a * b * c)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((a + b) * (a + c) * (b + c)) := by positivity
  have h_rational : (2) - (a / (b + a) + c / (a + c) + b / (b + c)) = (((a * (b ^ 2)) + (b * (c ^ 2)) + (c * (a ^ 2)) + (a * b * c))) / (((a + b) * (a + c) * (b + c))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
