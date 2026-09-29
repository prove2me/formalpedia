-- Prove2me | solution 1 for lean_workbook_plus_17115
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:03:50.576746+00:00
-- url     : https://prove2.me/submissions/fa047d5d-a884-4341-b738-fd5bb8479e73

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution : ∀ a b : ℝ, a ≥ 0 ∧ b ≥ 0 → (1 / (1 + a) ^ 2 + 1 / (1 + b) ^ 2) ≥ 2 / (a ^ 2 + b ^ 2 + 2) := by
  intro a b
  intros
  have p2m_cond_0 : (0 : ℝ) ≤ (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) ≤ (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (0) := by linarith only [p2m_cond_1]
  have h_identity : (2 + (a ^ 4) + (b ^ 4) + (2 * (a ^ 2)) + (2 * (a ^ 3)) + (2 * (b ^ 2)) + (2 * (b ^ 3)) + ((-8) * a * b) + ((-2) * a * (b ^ 2)) + ((-2) * b * (a ^ 2))) = (2 : ℝ) * 1 * ((1 + ((-1) * a * b)))^2 + (2 : ℝ) * 1 * ((a + ((-1) * b)))^2 + (1 : ℝ) * 1 * (((a ^ 2) + ((-1) * (b ^ 2))))^2 + (2 : ℝ) * ((a) - (0)) * ((a + ((-1) * b)))^2 + (2 : ℝ) * ((b) - (0)) * ((a + ((-1) * b)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (2 + (a ^ 4) + (b ^ 4) + (2 * (a ^ 2)) + (2 * (a ^ 3)) + (2 * (b ^ 2)) + (2 * (b ^ 3)) + ((-8) * a * b) + ((-2) * a * (b ^ 2)) + ((-2) * b * (a ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (((1 + a) ^ 2) * ((1 + b) ^ 2) * (2 + (a ^ 2) + (b ^ 2))) := by positivity
  have h_rational : ((1 / (1 + a) ^ 2 + 1 / (1 + b) ^ 2)) - (2 / (a ^ 2 + b ^ 2 + 2)) = ((2 + (a ^ 4) + (b ^ 4) + (2 * (a ^ 2)) + (2 * (a ^ 3)) + (2 * (b ^ 2)) + (2 * (b ^ 3)) + ((-8) * a * b) + ((-2) * a * (b ^ 2)) + ((-2) * b * (a ^ 2)))) / ((((1 + a) ^ 2) * ((1 + b) ^ 2) * (2 + (a ^ 2) + (b ^ 2)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
