-- Prove2me | solution 1 for lean_workbook_plus_34673
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:04:57.681894+00:00
-- url     : https://prove2.me/submissions/0f81719b-e9c2-4862-8a54-3cbbdc90734e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x : ℝ)
  (h₀ : 1 > x ∧ x ≥ 1 / 2) :
  (1 + 2 * x^2) / (1 - x^2) ≥ 2 := by
  intros
  have hxlo : 1/2 ≤ x := by aesop
  have hxhi : x < 1 := by aesop
  have hxone : 0 < 1+x := by linarith
  have hxsmall : 0 < 1-x := by linarith
  have hxsq : x^2 < 1 := by nlinarith [mul_pos hxone hxsmall]
  have p2m_cond_1 : (1 / 2 : ℝ) ≤ (x) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (x) - (1 / 2) := by linarith only [p2m_cond_1]
  have h_identity : ((-1) + (4 * (x ^ 2))) = (1 : ℝ) * 1 * ((1 + ((-2) * x)))^2 + (4 : ℝ) * ((x) - (1 / 2)) * (1)^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((-1) + (4 * (x ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((-1) * (1 + x) * ((-1) + x)) := by first | positivity | nlinarith | aesop
  have h_rational : ((1 + 2 * x^2) / (1 - x^2)) - (2) = (((-1) + (4 * (x ^ 2)))) / (((-1) * (1 + x) * ((-1) + x))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
