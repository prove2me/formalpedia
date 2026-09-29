-- Prove2me | solution 1 for lean_workbook_plus_35937
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:06:41.997438+00:00
-- url     : https://prove2.me/submissions/d7fd33d4-7ce1-4201-8eee-2f073d9383f5

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution {x y z : ℝ} (hx : 0 < x ∧ 0 < y ∧ 0 < z) (hx1 : y + z > x) (hx2 : z + x > y) (hx3 : x + y > z) : (x * y * z) / ((-x + y + z) * (x - y + z) * (x + y - z)) ≥ 1 := by
  intros
  have p2m_pos_x : (0 : ℝ) < x := by grind
  have p2m_pos_y : (0 : ℝ) < y := by grind
  have p2m_pos_z : (0 : ℝ) < z := by grind
  have p2m_pos_factor_0 : (0 : ℝ) < -x+y+z := by linarith
  have p2m_pos_factor_1 : (0 : ℝ) < x-y+z := by linarith
  have p2m_pos_factor_2 : (0 : ℝ) < x+y-z := by linarith
  have p2m_cond_3 : (x : ℝ) < (y + z) := by first | assumption | aesop | linarith
  have p2m_cond_3_gap : (0 : ℝ) ≤ (y + z) - (x) := by linarith only [p2m_cond_3]
  have p2m_cond_4 : (y : ℝ) < (z + x) := by first | assumption | aesop | linarith
  have p2m_cond_4_gap : (0 : ℝ) ≤ (z + x) - (y) := by linarith only [p2m_cond_4]
  have p2m_cond_5 : (z : ℝ) < (x + y) := by first | assumption | aesop | linarith
  have p2m_cond_5_gap : (0 : ℝ) ≤ (x + y) - (z) := by linarith only [p2m_cond_5]
  have h_identity : ((x ^ 3) + (y ^ 3) + (z ^ 3) + ((-1) * x * (y ^ 2)) + ((-1) * x * (z ^ 2)) + ((-1) * y * (x ^ 2)) + ((-1) * y * (z ^ 2)) + ((-1) * z * (x ^ 2)) + ((-1) * z * (y ^ 2)) + (3 * x * y * z)) = ((1 / 2) : ℝ) * ((y + z) - (x)) * ((y + ((-1) * z)))^2 + ((1 / 2) : ℝ) * ((z + x) - (y)) * ((x + ((-1) * z)))^2 + ((1 / 2) : ℝ) * ((x + y) - (z)) * ((x + ((-1) * y)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((x ^ 3) + (y ^ 3) + (z ^ 3) + ((-1) * x * (y ^ 2)) + ((-1) * x * (z ^ 2)) + ((-1) * y * (x ^ 2)) + ((-1) * y * (z ^ 2)) + ((-1) * z * (x ^ 2)) + ((-1) * z * (y ^ 2)) + (3 * x * y * z)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((-1) * (x + y + ((-1) * z)) * (x + z + ((-1) * y)) * (x + ((-1) * y) + ((-1) * z))) := by
    convert mul_pos (mul_pos p2m_pos_factor_0 p2m_pos_factor_1) p2m_pos_factor_2 using 1 <;> ring
  have h_rational : ((x * y * z) / ((-x + y + z) * (x - y + z) * (x + y - z))) - (1) = (((x ^ 3) + (y ^ 3) + (z ^ 3) + ((-1) * x * (y ^ 2)) + ((-1) * x * (z ^ 2)) + ((-1) * y * (x ^ 2)) + ((-1) * y * (z ^ 2)) + ((-1) * z * (x ^ 2)) + ((-1) * z * (y ^ 2)) + (3 * x * y * z))) / (((-1) * (x + y + ((-1) * z)) * (x + z + ((-1) * y)) * (x + ((-1) * y) + ((-1) * z)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
