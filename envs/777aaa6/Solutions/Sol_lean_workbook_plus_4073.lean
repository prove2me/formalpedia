-- Prove2me | solution 1 for lean_workbook_plus_4073
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:04:25.80177+00:00
-- url     : https://prove2.me/submissions/deff3b43-fa1d-4eb7-a728-901d80d19b8b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≥ 2 * b) : a^2 / b + b^2 / a ≥ 9 * a / 4 := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) < (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (2 * b : ℝ) ≤ (a) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (a) - (2 * b) := by linarith only [p2m_cond_2]
  have h_identity : ((4 * (a ^ 3)) + (4 * (b ^ 3)) + ((-9) * b * (a ^ 2))) = (1 : ℝ) * ((a) - (0)) * ((a + ((-2) * b)))^2 + (1 : ℝ) * ((b) - (0)) * ((a + ((-2) * b)))^2 + (3 : ℝ) * ((a) - (2 * b)) * (a)^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((4 * (a ^ 3)) + (4 * (b ^ 3)) + ((-9) * b * (a ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (4 * a * b) := by positivity
  have h_rational : (a^2 / b + b^2 / a) - (9 * a / 4) = (((4 * (a ^ 3)) + (4 * (b ^ 3)) + ((-9) * b * (a ^ 2)))) / ((4 * a * b)) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
