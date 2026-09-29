-- Prove2me | solution 1 for lean_workbook_plus_12117
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:04:06.461504+00:00
-- url     : https://prove2.me/submissions/82d6376d-26e1-4e50-9f90-67bb4aef4ec4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) (ha : a > 0) (hb : b > 0) (hab : a + b > 1) : 1 / (a + b - 1) + a / b + b / a ≥ 1 + 1 / a + 1 / b := by
  intros
  have p2m_pos_a : (0 : ℝ) < a := by grind
  have p2m_pos_b : (0 : ℝ) < b := by grind
  have p2m_pos_factor_0 : (0 : ℝ) < -1+a+b := by linarith
  have p2m_cond_0 : (0 : ℝ) < (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) < (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (0) := by linarith only [p2m_cond_1]
  have h_identity : (a + b + (a ^ 3) + (b ^ 3) + ((-2) * (a ^ 2)) + ((-2) * (b ^ 2))) = (1 : ℝ) * ((a) - (0)) * ((1 + ((-1) * a)))^2 + (1 : ℝ) * ((b) - (0)) * ((1 + ((-1) * b)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (a + b + (a ^ 3) + (b ^ 3) + ((-2) * (a ^ 2)) + ((-2) * (b ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (a * b * ((-1) + a + b)) := by positivity
  have h_rational : (1 / (a + b - 1) + a / b + b / a) - (1 + 1 / a + 1 / b) = ((a + b + (a ^ 3) + (b ^ 3) + ((-2) * (a ^ 2)) + ((-2) * (b ^ 2)))) / ((a * b * ((-1) + a + b))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
