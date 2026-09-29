-- Prove2me | solution 1 for lean_workbook_plus_2941
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:09:46.449788+00:00
-- url     : https://prove2.me/submissions/8c842ea8-776e-4746-a522-5eb43176d9b9

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
  4 / (x^2 + y * z) ≤ 1 / (x * y) + 1 / (x * z) := by
  intros
  have hx0 : 0 < x := by aesop
  have hy0 : 0 < y := by aesop
  have hz0 : 0 < z := by aesop
  have p2m_cond_1 : (0 : ℝ) < (y) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (y) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (0 : ℝ) < (z) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (z) - (0) := by linarith only [p2m_cond_2]
  have h_identity : ((y * (x ^ 2)) + (y * (z ^ 2)) + (z * (x ^ 2)) + (z * (y ^ 2)) + ((-4) * x * y * z)) = (1 : ℝ) * ((y) - (0)) * ((x + ((-1) * z)))^2 + (1 : ℝ) * ((z) - (0)) * ((x + ((-1) * y)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((y * (x ^ 2)) + (y * (z ^ 2)) + (z * (x ^ 2)) + (z * (y ^ 2)) + ((-4) * x * y * z)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (x * y * z * ((x ^ 2) + (y * z))) := by first | positivity | nlinarith | aesop
  have h_rational : (1 / (x * y) + 1 / (x * z)) - (4 / (x^2 + y * z)) = (((y * (x ^ 2)) + (y * (z ^ 2)) + (z * (x ^ 2)) + (z * (y ^ 2)) + ((-4) * x * y * z))) / ((x * y * z * ((x ^ 2) + (y * z)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
