-- Prove2me | solution 1 for lean_workbook_plus_42072
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:51.127476+00:00
-- url     : https://prove2.me/submissions/a192dc85-74a0-400b-9921-76788e249e52

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y z : ℝ) (hx : x + y + z = 1) (hx' : 0 ≤ x) (hy' : 0 ≤ y) (hz' : 0 ≤ z) : 1 / (x ^ 2 + 1) ≤ (54 - 27 * x) / 50 := by
  intros
  have p2m_cond_2 : (0 : ℝ) ≤ (y) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (y) - (0) := by linarith only [p2m_cond_2]
  have p2m_cond_3 : (0 : ℝ) ≤ (z) := by first | assumption | aesop | linarith
  have p2m_cond_3_gap : (0 : ℝ) ≤ (z) - (0) := by linarith only [p2m_cond_3]
  have p2m_cond_0 : (x + y + z : ℝ) = (1) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (1) - (x + y + z) = 0 := by linarith only [p2m_cond_0]
  have h_identity : (4 + ((-27) * x) + ((-27) * (x ^ 3)) + (54 * (x ^ 2))) = (4 : ℝ) * 1 * ((x + ((-1 / 2) * y) + ((-1 / 2) * z)))^2 + (12 : ℝ) * ((y) - (0)) * ((x + ((-1 / 2) * y) + ((-1 / 2) * z)))^2 + (12 : ℝ) * ((z) - (0)) * ((x + ((-1 / 2) * y) + ((-1 / 2) * z)))^2 := by
    linear_combination ((4 + ((-23) * x) + (3 * (y ^ 2)) + (3 * (z ^ 2)) + (4 * y) + (4 * z) + (27 * (x ^ 2)) + ((-15) * x * y) + ((-15) * x * z) + (6 * y * z))) * p2m_cond_0_gap
  have h_nonnegative : (0 : ℝ) ≤ (4 + ((-27) * x) + ((-27) * (x ^ 3)) + (54 * (x ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (50 * (1 + (x ^ 2))) := by positivity
  have h_rational : ((54 - 27 * x) / 50) - (1 / (x ^ 2 + 1)) = ((4 + ((-27) * x) + ((-27) * (x ^ 3)) + (54 * (x ^ 2)))) / ((50 * (1 + (x ^ 2)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
