-- Prove2me | solution 1 for lean_workbook_plus_39418
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:30:46.045903+00:00
-- url     : https://prove2.me/submissions/615cf5b8-1d9a-4907-864f-a2ec3b3ed19e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : 8 / a + 27 / b ^ 2 ≥ 80 := by
  intros
  have p2m_cond_1 : (0 : ℝ) < (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (a + b : ℝ) = (1) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (1) - (a + b) = 0 := by linarith only [p2m_cond_2]
  have h_identity : ((8 * (b ^ 2)) + (27 * a) + ((-80) * a * (b ^ 2))) = ((4 / 3) : ℝ) * 1 * ((1 + ((-5 / 2) * b) + ((7 / 2) * a)))^2 + ((20 / 9) : ℝ) * ((b) - (0)) * ((1 + ((-5 / 2) * b) + ((7 / 2) * a)))^2 := by
    linear_combination (((-4 / 3) + ((28 / 9) * b) + ((49 / 3) * a) + ((125 / 9) * (b ^ 2)) + ((245 / 9) * a * b))) * p2m_cond_2_gap
  have h_nonnegative : (0 : ℝ) ≤ ((8 * (b ^ 2)) + (27 * a) + ((-80) * a * (b ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (a * (b ^ 2)) := by positivity
  have h_rational : (8 / a + 27 / b ^ 2) - (80) = (((8 * (b ^ 2)) + (27 * a) + ((-80) * a * (b ^ 2)))) / ((a * (b ^ 2))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
