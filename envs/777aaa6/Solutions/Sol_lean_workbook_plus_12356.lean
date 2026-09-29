-- Prove2me | solution 1 for lean_workbook_plus_12356
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:07:13.245334+00:00
-- url     : https://prove2.me/submissions/c335c32f-e146-456e-85c8-a848b668bf28

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) (ha : 1 < a) (hb : 1 < b) : a / (b - 1) + b / (a - 1) ≥ 2 * (a + b) / (a + b - 2) := by
  intros
  have p2m_pos_a : (0 : ℝ) < a := by grind
  have p2m_pos_b : (0 : ℝ) < b := by grind
  have p2m_pos_factor_0 : (0 : ℝ) < -1+a := by linarith
  have p2m_pos_factor_1 : (0 : ℝ) < -1+b := by linarith
  have p2m_pos_factor_2 : (0 : ℝ) < -2+a+b := by linarith
  have p2m_cond_0 : (1 : ℝ) < (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (1) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (1 : ℝ) < (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (1) := by linarith only [p2m_cond_1]
  have h_identity : ((a ^ 3) + (b ^ 3) + ((-1) * (a ^ 2)) + ((-1) * (b ^ 2)) + ((-1) * a * (b ^ 2)) + ((-1) * b * (a ^ 2)) + (2 * a * b)) = (1 : ℝ) * 1 * ((a + ((-1) * b)))^2 + (1 : ℝ) * ((a) - (1)) * ((a + ((-1) * b)))^2 + (1 : ℝ) * ((b) - (1)) * ((a + ((-1) * b)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a ^ 3) + (b ^ 3) + ((-1) * (a ^ 2)) + ((-1) * (b ^ 2)) + ((-1) * a * (b ^ 2)) + ((-1) * b * (a ^ 2)) + (2 * a * b)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (((-1) + a) * ((-1) + b) * ((-2) + a + b)) := by positivity
  have h_rational : (a / (b - 1) + b / (a - 1)) - (2 * (a + b) / (a + b - 2)) = (((a ^ 3) + (b ^ 3) + ((-1) * (a ^ 2)) + ((-1) * (b ^ 2)) + ((-1) * a * (b ^ 2)) + ((-1) * b * (a ^ 2)) + (2 * a * b))) / ((((-1) + a) * ((-1) + b) * ((-2) + a + b))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
