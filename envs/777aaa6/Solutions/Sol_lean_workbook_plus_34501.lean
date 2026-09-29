-- Prove2me | solution 1 for lean_workbook_plus_34501
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:11:02.167469+00:00
-- url     : https://prove2.me/submissions/b22a3d27-f281-442b-8331-256186817526

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → a / (a ^ 2 + b * c) ≤ (1 / 4) * (1 / b + 1 / c) := by
  intro a b c
  intros
  have p2m_cond_1 : (0 : ℝ) < (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (0 : ℝ) < (c) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (c) - (0) := by linarith only [p2m_cond_2]
  have h_identity : ((b * (a ^ 2)) + (b * (c ^ 2)) + (c * (a ^ 2)) + (c * (b ^ 2)) + ((-4) * a * b * c)) = (1 : ℝ) * ((b) - (0)) * ((a + ((-1) * c)))^2 + (1 : ℝ) * ((c) - (0)) * ((a + ((-1) * b)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((b * (a ^ 2)) + (b * (c ^ 2)) + (c * (a ^ 2)) + (c * (b ^ 2)) + ((-4) * a * b * c)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (4 * b * c * ((a ^ 2) + (b * c))) := by positivity
  have h_rational : ((1 / 4) * (1 / b + 1 / c)) - (a / (a ^ 2 + b * c)) = (((b * (a ^ 2)) + (b * (c ^ 2)) + (c * (a ^ 2)) + (c * (b ^ 2)) + ((-4) * a * b * c))) / ((4 * b * c * ((a ^ 2) + (b * c)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
