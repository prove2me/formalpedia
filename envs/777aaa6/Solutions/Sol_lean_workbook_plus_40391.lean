-- Prove2me | solution 1 for lean_workbook_plus_40391
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:10:27.531722+00:00
-- url     : https://prove2.me/submissions/d6466ce9-d2f7-4bd2-bb90-ee9c9c519a2c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x : ℝ) (hx: 0 < x ∧ x < 4) : (4 - x) / x + x / (4 - x) ≥ 62 / 9 - 32 * x / 9 := by
  intros
  have p2m_pos_x : (0 : ℝ) < x := by grind
  have p2m_pos_factor_0 : (0 : ℝ) < 4-x := by nlinarith
  have p2m_cond_0 : (0 : ℝ) < (x) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (x) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (x : ℝ) < (4) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (4) - (x) := by linarith only [p2m_cond_1]
  have h_identity : (144 + ((-320) * x) + ((-32) * (x ^ 3)) + (208 * (x ^ 2))) = (4 : ℝ) * ((x) - (0)) * ((1 + ((-1) * x)))^2 + (36 : ℝ) * ((4) - (x)) * ((1 + ((-1) * x)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (144 + ((-320) * x) + ((-32) * (x ^ 3)) + (208 * (x ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((-9) * x * ((-4) + x)) := by
    convert mul_pos (mul_pos (show (0 : ℝ) < 9 by norm_num) p2m_pos_x) p2m_pos_factor_0 using 1 <;> ring
  have h_rational : ((4 - x) / x + x / (4 - x)) - (62 / 9 - 32 * x / 9) = ((144 + ((-320) * x) + ((-32) * (x ^ 3)) + (208 * (x ^ 2)))) / (((-9) * x * ((-4) + x))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
