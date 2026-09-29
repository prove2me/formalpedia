-- Prove2me | solution 1 for lean_workbook_plus_28706
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:09:18.722856+00:00
-- url     : https://prove2.me/submissions/2ef862d3-5c85-4300-8b11-0c2f756b2bcf

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y z : ℝ) (hx : x > 0 ∧ y > 0 ∧ z > 0 ∧ x*y*z ≥ 1) : x/(x+y+z) ≥ x^2/(x^5+y^2+z^2) := by
  intros
  have p2m_pos_x : (0 : ℝ) < x := by grind
  have p2m_pos_y : (0 : ℝ) < y := by grind
  have p2m_pos_z : (0 : ℝ) < z := by grind
  
  have p2m_cond_0 : (0 : ℝ) < (x) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (x) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_3 : (1 : ℝ) ≤ (x*y*z) := by first | assumption | aesop | linarith
  have p2m_cond_3_gap : (0 : ℝ) ≤ (x*y*z) - (1) := by linarith only [p2m_cond_3]
  have h_identity : ((x ^ 6) + ((-1) * (x ^ 3)) + (x * (y ^ 2)) + (x * (z ^ 2)) + ((-1) * y * (x ^ 2)) + ((-1) * z * (x ^ 2))) = (1 : ℝ) * 1 * ((1 + ((-1) * (x ^ 3))))^2 + ((1 / 2) : ℝ) * ((x) - (0)) * ((x + ((-1) * y)))^2 + ((1 / 2) : ℝ) * ((x) - (0)) * ((x + ((-1) * z)))^2 + ((1 / 2) : ℝ) * ((x) - (0)) * ((y + ((-1) * z)))^2 + (1 : ℝ) * ((x*y*z) - (1)) * (1)^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((x ^ 6) + ((-1) * (x ^ 3)) + (x * (y ^ 2)) + (x * (z ^ 2)) + ((-1) * y * (x ^ 2)) + ((-1) * z * (x ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((x + y + z) * ((x ^ 5) + (y ^ 2) + (z ^ 2))) := by positivity
  have h_rational : (x/(x+y+z)) - (x^2/(x^5+y^2+z^2)) = (((x ^ 6) + ((-1) * (x ^ 3)) + (x * (y ^ 2)) + (x * (z ^ 2)) + ((-1) * y * (x ^ 2)) + ((-1) * z * (x ^ 2)))) / (((x + y + z) * ((x ^ 5) + (y ^ 2) + (z ^ 2)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
