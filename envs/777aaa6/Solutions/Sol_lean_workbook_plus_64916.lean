-- Prove2me | solution 1 for lean_workbook_plus_64916
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:15:29.487109+00:00
-- url     : https://prove2.me/submissions/ea11dc5e-cbf9-40f5-b7df-64e5d6e546d0

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → a / (2 * a + b + c) + b / (2 * b + c + a) + c / (2 * c + a + b) ≤ 3 / 4 := by
  intro a b c
  intros
  have p2m_cond_0 : (0 : ℝ) < (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) < (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (0 : ℝ) < (c) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (c) - (0) := by linarith only [p2m_cond_2]
  have h_identity : ((2 * (a ^ 3)) + (2 * (b ^ 3)) + (2 * (c ^ 3)) + (a * (b ^ 2)) + (a * (c ^ 2)) + (b * (a ^ 2)) + (b * (c ^ 2)) + (c * (a ^ 2)) + (c * (b ^ 2)) + ((-12) * a * b * c)) = (2 : ℝ) * ((a) - (0)) * ((a + ((-1) * c)))^2 + (3 : ℝ) * ((a) - (0)) * ((b + ((-1) * c)))^2 + (1 : ℝ) * ((b) - (0)) * ((a + ((-1) * b)))^2 + (1 : ℝ) * ((b) - (0)) * ((b + ((-1) * c)))^2 + (3 : ℝ) * ((c) - (0)) * ((a + ((-1) * b)))^2 + (2 : ℝ) * ((c) - (0)) * ((a + ((-1) * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((2 * (a ^ 3)) + (2 * (b ^ 3)) + (2 * (c ^ 3)) + (a * (b ^ 2)) + (a * (c ^ 2)) + (b * (a ^ 2)) + (b * (c ^ 2)) + (c * (a ^ 2)) + (c * (b ^ 2)) + ((-12) * a * b * c)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (4 * (a + b + (2 * c)) * (a + c + (2 * b)) * (b + c + (2 * a))) := by positivity
  have h_rational : (3 / 4) - (a / (2 * a + b + c) + b / (2 * b + c + a) + c / (2 * c + a + b)) = (((2 * (a ^ 3)) + (2 * (b ^ 3)) + (2 * (c ^ 3)) + (a * (b ^ 2)) + (a * (c ^ 2)) + (b * (a ^ 2)) + (b * (c ^ 2)) + (c * (a ^ 2)) + (c * (b ^ 2)) + ((-12) * a * b * c))) / ((4 * (a + b + (2 * c)) * (a + c + (2 * b)) * (b + c + (2 * a)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
