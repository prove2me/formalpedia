-- Prove2me | solution 1 for lean_workbook_plus_45619
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:46.033715+00:00
-- url     : https://prove2.me/submissions/17152dc4-fbab-45fb-b081-3c9c33005265

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : a + b + 25 / (4 * (a ^ 2 + a * b + b + 1)) ≥ 13 / 4 := by
  intros
  have p2m_cond_0 : (0 : ℝ) ≤ (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) ≤ (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (0) := by linarith only [p2m_cond_1]
  have h_identity : (12 + ((-13) * (a ^ 2)) + ((-9) * b) + (4 * a) + (4 * (a ^ 3)) + (4 * (b ^ 2)) + ((-9) * a * b) + (4 * a * (b ^ 2)) + (8 * b * (a ^ 2))) = (12 : ℝ) * 1 * ((1 + ((-23 / 60) * b) + ((-1 / 2) * a)))^2 + ((671 / 300) : ℝ) * 1 * (b)^2 + (16 : ℝ) * ((a) - (0)) * ((1 + ((-9 / 20) * b) + ((-1 / 2) * a)))^2 + ((19 / 25) : ℝ) * ((a) - (0)) * (b)^2 + ((1 / 5) : ℝ) * ((b) - (0)) * ((1 + (2 * a)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (12 + ((-13) * (a ^ 2)) + ((-9) * b) + (4 * a) + (4 * (a ^ 3)) + (4 * (b ^ 2)) + ((-9) * a * b) + (4 * a * (b ^ 2)) + (8 * b * (a ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (4 * (1 + b + (a ^ 2) + (a * b))) := by positivity
  have h_rational : (a + b + 25 / (4 * (a ^ 2 + a * b + b + 1))) - (13 / 4) = ((12 + ((-13) * (a ^ 2)) + ((-9) * b) + (4 * a) + (4 * (a ^ 3)) + (4 * (b ^ 2)) + ((-9) * a * b) + (4 * a * (b ^ 2)) + (8 * b * (a ^ 2)))) / ((4 * (1 + b + (a ^ 2) + (a * b)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
