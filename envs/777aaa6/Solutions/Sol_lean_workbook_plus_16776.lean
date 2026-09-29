-- Prove2me | solution 1 for lean_workbook_plus_16776
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:04:00.252021+00:00
-- url     : https://prove2.me/submissions/bc0b3441-7279-4b87-9fa7-a22e62cb5924

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hxy : x + y = z) : x * y / z ^ 2 + y / x + x / y ≥ 9 / 4 := by
  intros
  have p2m_cond_3 : (x + y : ℝ) = (z) := by first | assumption | aesop | linarith
  have p2m_cond_3_gap : (z) - (x + y) = 0 := by linarith only [p2m_cond_3]
  have h_identity : ((4 * (x ^ 2) * (y ^ 2)) + (4 * (x ^ 2) * (z ^ 2)) + (4 * (y ^ 2) * (z ^ 2)) + ((-9) * x * y * (z ^ 2))) = ((1 / 2) : ℝ) * 1 * (((x ^ 2) + ((-1) * x * y)))^2 + ((1 / 2) : ℝ) * 1 * ((((-1) * (y ^ 2)) + (x * y)))^2 + ((7 / 2) : ℝ) * 1 * (((x * z) + ((-1) * y * z)))^2 := by
    linear_combination ((((1 / 2) * (x ^ 3)) + ((1 / 2) * (y ^ 3)) + ((1 / 2) * z * (x ^ 2)) + ((1 / 2) * z * (y ^ 2)) + ((-3 / 2) * x * (y ^ 2)) + ((-3 / 2) * y * (x ^ 2)) + ((-2) * x * y * z))) * p2m_cond_3_gap
  have h_nonnegative : (0 : ℝ) ≤ ((4 * (x ^ 2) * (y ^ 2)) + (4 * (x ^ 2) * (z ^ 2)) + (4 * (y ^ 2) * (z ^ 2)) + ((-9) * x * y * (z ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (4 * x * y * (z ^ 2)) := by positivity
  have h_rational : (x * y / z ^ 2 + y / x + x / y) - (9 / 4) = (((4 * (x ^ 2) * (y ^ 2)) + (4 * (x ^ 2) * (z ^ 2)) + (4 * (y ^ 2) * (z ^ 2)) + ((-9) * x * y * (z ^ 2)))) / ((4 * x * y * (z ^ 2))) := by
    field_simp (disch := positivity)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
