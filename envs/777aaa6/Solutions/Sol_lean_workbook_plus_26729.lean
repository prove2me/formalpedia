-- Prove2me | solution 1 for lean_workbook_plus_26729
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:09:01.75055+00:00
-- url     : https://prove2.me/submissions/6a35c04b-80e0-44e1-b4fd-441a61f76ae1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : (2 + a) / (2 - a) + (2 + b) / (2 - b) ≥ 10 / 3 := by
  intros
  have p2m_pos_a : (0 : ℝ) < a := by grind
  have p2m_pos_b : (0 : ℝ) < b := by grind
  have p2m_pos_factor_0 : (0 : ℝ) < 2-a := by nlinarith
  have p2m_pos_factor_1 : (0 : ℝ) < 2-b := by nlinarith
  have p2m_cond_2 : (a + b : ℝ) = (1) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (1) - (a + b) = 0 := by linarith only [p2m_cond_2]
  have h_identity : ((-16) + (20 * a) + (20 * b) + ((-16) * a * b)) = (4 : ℝ) * 1 * ((a + ((-1) * b)))^2 := by
    linear_combination (((-16) + (4 * a) + (4 * b))) * p2m_cond_2_gap
  have h_nonnegative : (0 : ℝ) ≤ ((-16) + (20 * a) + (20 * b) + ((-16) * a * b)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (3 * ((-2) + a) * ((-2) + b)) := by
    convert mul_pos (mul_pos (show (0 : ℝ) < 3 by norm_num) p2m_pos_factor_0) p2m_pos_factor_1 using 1 <;> ring
  have h_rational : ((2 + a) / (2 - a) + (2 + b) / (2 - b)) - (10 / 3) = (((-16) + (20 * a) + (20 * b) + ((-16) * a * b))) / ((3 * ((-2) + a) * ((-2) + b))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
