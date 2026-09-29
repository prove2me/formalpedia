-- Prove2me | solution 1 for lean_workbook_plus_42857
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:10:13.851368+00:00
-- url     : https://prove2.me/submissions/d2d0daee-ccc1-4f2a-baaa-7f08deafd7ae

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : x^5 - x^2 + 3 ≥ x^3 + 2) :
  1 / (x^5 - x^2 + 3) ≤ 1 / (x^3 + 2) := by
  intros
  have p2m_pos_x : (0 : ℝ) < x := by grind
  have p2m_pos_factor_0 : (0 : ℝ) < 3+x^5-x^2 := by nlinarith [pow_pos p2m_pos_x 3]
  have p2m_cond_0 : (0 : ℝ) < (x) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (x) - (0) := by linarith only [p2m_cond_0]
  have h_identity : (1 + (x ^ 5) + ((-1) * (x ^ 2)) + ((-1) * (x ^ 3))) = ((1 / 3) : ℝ) * 1 * ((1 + ((-1) * x)))^2 + ((2 / 3) : ℝ) * 1 * ((1 + ((-1) * (x ^ 2))))^2 + ((2 / 3) : ℝ) * ((x) - (0)) * ((1 + ((-1) * (x ^ 2))))^2 + ((1 / 3) : ℝ) * ((x) - (0)) * ((x + ((-1) * (x ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (1 + (x ^ 5) + ((-1) * (x ^ 2)) + ((-1) * (x ^ 3))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((2 + (x ^ 3)) * (3 + (x ^ 5) + ((-1) * (x ^ 2)))) := by
    convert mul_pos (show (0 : ℝ) < 2+x^3 by positivity) p2m_pos_factor_0 using 1 <;> ring
  have h_rational : (1 / (x^3 + 2)) - (1 / (x^5 - x^2 + 3)) = ((1 + (x ^ 5) + ((-1) * (x ^ 2)) + ((-1) * (x ^ 3)))) / (((2 + (x ^ 3)) * (3 + (x ^ 5) + ((-1) * (x ^ 2))))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
