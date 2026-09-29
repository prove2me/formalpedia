-- Prove2me | solution 1 for lean_workbook_plus_5855
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:08:50.761701+00:00
-- url     : https://prove2.me/submissions/d9c8705a-871e-45be-981c-86dc7abbc0fe

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y z : ℝ) : (x + y + z > 0 ∧ x > 0 ∧ y > 0 ∧ z > 0) → 2 / (x + y) + 2 / (y + z) + 2 / (x + z) ≥ 9 / (x + y + z) := by
  intros
  have p2m_cond_1 : (0 : ℝ) < (x) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (x) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (0 : ℝ) < (y) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (y) - (0) := by linarith only [p2m_cond_2]
  have p2m_cond_3 : (0 : ℝ) < (z) := by first | assumption | aesop | linarith
  have p2m_cond_3_gap : (0 : ℝ) ≤ (z) - (0) := by linarith only [p2m_cond_3]
  have h_identity : ((2 * (x ^ 3)) + (2 * (y ^ 3)) + (2 * (z ^ 3)) + ((-1) * x * (y ^ 2)) + ((-1) * x * (z ^ 2)) + ((-1) * y * (x ^ 2)) + ((-1) * y * (z ^ 2)) + ((-1) * z * (x ^ 2)) + ((-1) * z * (y ^ 2))) = (1 : ℝ) * ((x) - (0)) * ((x + ((-1) * y)))^2 + (1 : ℝ) * ((x) - (0)) * ((x + ((-1) * z)))^2 + (1 : ℝ) * ((y) - (0)) * ((x + ((-1) * y)))^2 + (1 : ℝ) * ((y) - (0)) * ((y + ((-1) * z)))^2 + (1 : ℝ) * ((z) - (0)) * ((x + ((-1) * z)))^2 + (1 : ℝ) * ((z) - (0)) * ((y + ((-1) * z)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((2 * (x ^ 3)) + (2 * (y ^ 3)) + (2 * (z ^ 3)) + ((-1) * x * (y ^ 2)) + ((-1) * x * (z ^ 2)) + ((-1) * y * (x ^ 2)) + ((-1) * y * (z ^ 2)) + ((-1) * z * (x ^ 2)) + ((-1) * z * (y ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((x + y) * (x + z) * (y + z) * (x + y + z)) := by positivity
  have h_rational : (2 / (x + y) + 2 / (y + z) + 2 / (x + z)) - (9 / (x + y + z)) = (((2 * (x ^ 3)) + (2 * (y ^ 3)) + (2 * (z ^ 3)) + ((-1) * x * (y ^ 2)) + ((-1) * x * (z ^ 2)) + ((-1) * y * (x ^ 2)) + ((-1) * y * (z ^ 2)) + ((-1) * z * (x ^ 2)) + ((-1) * z * (y ^ 2)))) / (((x + y) * (x + z) * (y + z) * (x + y + z))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
