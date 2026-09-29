-- Prove2me | solution 1 for lean_workbook_plus_21709
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:45.87446+00:00
-- url     : https://prove2.me/submissions/2ab13a5e-bc1f-4068-84ba-5e3a67e59fce

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a^2 + b^2 ≥ 2) : a / (a^2 + b) + b / (b^2 + a) ≤ 1 := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) < (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (2 : ℝ) ≤ (a^2 + b^2) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (a^2 + b^2) - (2) := by linarith only [p2m_cond_2]
  have h_identity : ((a ^ 3) + (b ^ 3) + ((-1) * (a ^ 2)) + ((-1) * (b ^ 2)) + (a * b) + ((a ^ 2) * (b ^ 2)) + ((-1) * a * (b ^ 2)) + ((-1) * b * (a ^ 2))) = (1 : ℝ) * 1 * ((1 + ((-1 / 2) * a) + ((-1 / 2) * b)))^2 + ((1 / 4) : ℝ) * 1 * ((a + b + ((-2) * a * b)))^2 + (1 : ℝ) * ((a) - (0)) * ((1 + ((-1) * a)))^2 + (1 : ℝ) * ((b) - (0)) * ((1 + ((-1) * b)))^2 + ((1 / 2) : ℝ) * ((a^2 + b^2) - (2)) * (1)^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a ^ 3) + (b ^ 3) + ((-1) * (a ^ 2)) + ((-1) * (b ^ 2)) + (a * b) + ((a ^ 2) * (b ^ 2)) + ((-1) * a * (b ^ 2)) + ((-1) * b * (a ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((a + (b ^ 2)) * (b + (a ^ 2))) := by positivity
  have h_rational : (1) - (a / (a^2 + b) + b / (b^2 + a)) = (((a ^ 3) + (b ^ 3) + ((-1) * (a ^ 2)) + ((-1) * (b ^ 2)) + (a * b) + ((a ^ 2) * (b ^ 2)) + ((-1) * a * (b ^ 2)) + ((-1) * b * (a ^ 2)))) / (((a + (b ^ 2)) * (b + (a ^ 2)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
