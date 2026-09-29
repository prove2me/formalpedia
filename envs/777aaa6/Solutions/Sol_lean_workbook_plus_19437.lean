-- Prove2me | solution 1 for lean_workbook_plus_19437
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:07.005921+00:00
-- url     : https://prove2.me/submissions/1dd97ae7-07c1-490b-93e5-58310f8f472d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) (hab : a * b = 1) : a / (a ^ 2 + 3) + b / (b ^ 2 + 3) ≤ 1 / 2 := by
  intros
  have p2m_cond_0 : (a * b : ℝ) = (1) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (1) - (a * b) = 0 := by linarith only [p2m_cond_0]
  have h_identity : (9 + ((-6) * a) + ((-6) * b) + (3 * (a ^ 2)) + (3 * (b ^ 2)) + ((a ^ 2) * (b ^ 2)) + ((-2) * a * (b ^ 2)) + ((-2) * b * (a ^ 2))) = (2 : ℝ) * 1 * ((1 + ((-1) * a) + ((-1) * b) + (a * b)))^2 + (1 : ℝ) * 1 * ((a + ((-1) * b)))^2 := by
    linear_combination ((7 + ((-2) * a) + ((-2) * b) + (a * b))) * p2m_cond_0_gap
  have h_nonnegative : (0 : ℝ) ≤ (9 + ((-6) * a) + ((-6) * b) + (3 * (a ^ 2)) + (3 * (b ^ 2)) + ((a ^ 2) * (b ^ 2)) + ((-2) * a * (b ^ 2)) + ((-2) * b * (a ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (2 * (3 + (a ^ 2)) * (3 + (b ^ 2))) := by positivity
  have h_rational : (1 / 2) - (a / (a ^ 2 + 3) + b / (b ^ 2 + 3)) = ((9 + ((-6) * a) + ((-6) * b) + (3 * (a ^ 2)) + (3 * (b ^ 2)) + ((a ^ 2) * (b ^ 2)) + ((-2) * a * (b ^ 2)) + ((-2) * b * (a ^ 2)))) / ((2 * (3 + (a ^ 2)) * (3 + (b ^ 2)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
