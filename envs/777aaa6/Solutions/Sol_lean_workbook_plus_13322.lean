-- Prove2me | solution 1 for lean_workbook_plus_13322
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:08:48.063099+00:00
-- url     : https://prove2.me/submissions/4132be1f-5503-4ab0-abe1-d1f845decb82

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
  1 / x + 1 / y + 1 / z ≥ (4 * (x + y + z) ^ 2 - 3 * (x * y + y * z + z * x)) / ((x + y + z) * (x * y + y * z + z * x)) := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (x) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (x) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) < (y) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (y) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (0 : ℝ) < (z) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (z) - (0) := by linarith only [p2m_cond_2]
  have h_identity : (((x ^ 2) * (y ^ 3)) + ((x ^ 2) * (z ^ 3)) + ((x ^ 3) * (y ^ 2)) + ((x ^ 3) * (z ^ 2)) + ((y ^ 2) * (z ^ 3)) + ((y ^ 3) * (z ^ 2)) + ((-2) * x * y * (z ^ 3)) + ((-2) * x * z * (y ^ 3)) + ((-2) * y * z * (x ^ 3))) = (1 : ℝ) * ((x) - (0)) * (((x * y) + ((-1) * x * z)))^2 + (1 : ℝ) * ((y) - (0)) * (((x * y) + ((-1) * y * z)))^2 + (1 : ℝ) * ((z) - (0)) * (((x * z) + ((-1) * y * z)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (((x ^ 2) * (y ^ 3)) + ((x ^ 2) * (z ^ 3)) + ((x ^ 3) * (y ^ 2)) + ((x ^ 3) * (z ^ 2)) + ((y ^ 2) * (z ^ 3)) + ((y ^ 3) * (z ^ 2)) + ((-2) * x * y * (z ^ 3)) + ((-2) * x * z * (y ^ 3)) + ((-2) * y * z * (x ^ 3))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (x * y * z * (x + y + z) * ((x * y) + (x * z) + (y * z))) := by positivity
  have h_rational : (1 / x + 1 / y + 1 / z) - ((4 * (x + y + z) ^ 2 - 3 * (x * y + y * z + z * x)) / ((x + y + z) * (x * y + y * z + z * x))) = ((((x ^ 2) * (y ^ 3)) + ((x ^ 2) * (z ^ 3)) + ((x ^ 3) * (y ^ 2)) + ((x ^ 3) * (z ^ 2)) + ((y ^ 2) * (z ^ 3)) + ((y ^ 3) * (z ^ 2)) + ((-2) * x * y * (z ^ 3)) + ((-2) * x * z * (y ^ 3)) + ((-2) * y * z * (x ^ 3)))) / ((x * y * z * (x + y + z) * ((x * y) + (x * z) + (y * z)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
