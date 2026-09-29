-- Prove2me | solution 1 for lean_workbook_plus_54346
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:11.151184+00:00
-- url     : https://prove2.me/submissions/9ec8c060-5f9e-416b-a5f6-1b0fcbf6f4d3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) ^ 2 + (a + b + c) ^ 2 ≥ 100 * a * b * c / (4 * a + 4 * b + c) := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) < (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (0 : ℝ) < (c) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (c) - (0) := by linarith only [p2m_cond_2]
  have h_identity : ((c ^ 3) + (8 * (a ^ 3)) + (8 * (b ^ 3)) + (6 * a * (c ^ 2)) + (6 * b * (c ^ 2)) + (10 * c * (a ^ 2)) + (10 * c * (b ^ 2)) + (24 * a * (b ^ 2)) + (24 * b * (a ^ 2)) + ((-80) * a * b * c)) = (8 : ℝ) * ((a) - (0)) * ((a + b + ((-1) * c)))^2 + (8 : ℝ) * ((b) - (0)) * ((a + b + ((-1) * c)))^2 + (26 : ℝ) * ((c) - (0)) * ((a + ((-12 / 13) * b) + ((-1 / 26) * c)))^2 + ((50 / 13) : ℝ) * ((c) - (0)) * ((b + ((-1 / 2) * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((c ^ 3) + (8 * (a ^ 3)) + (8 * (b ^ 3)) + (6 * a * (c ^ 2)) + (6 * b * (c ^ 2)) + (10 * c * (a ^ 2)) + (10 * c * (b ^ 2)) + (24 * a * (b ^ 2)) + (24 * b * (a ^ 2)) + ((-80) * a * b * c)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (c + (4 * a) + (4 * b)) := by positivity
  have h_rational : ((a + b) ^ 2 + (a + b + c) ^ 2) - (100 * a * b * c / (4 * a + 4 * b + c)) = (((c ^ 3) + (8 * (a ^ 3)) + (8 * (b ^ 3)) + (6 * a * (c ^ 2)) + (6 * b * (c ^ 2)) + (10 * c * (a ^ 2)) + (10 * c * (b ^ 2)) + (24 * a * (b ^ 2)) + (24 * b * (a ^ 2)) + ((-80) * a * b * c))) / ((c + (4 * a) + (4 * b))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
