-- Prove2me | solution 1 for lean_workbook_plus_32025
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:52:36.785692+00:00
-- url     : https://prove2.me/submissions/5dcea21d-6dec-4054-9a15-fa9914d92834

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ)
  (h₀ : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c)
  (h₁ : a + b + c = 0) :
  a * b^3 + b * c^3 + c * a^3 ≤ 0 := by
  clear h₀
  intros
  have p2m_cond_3 : (a + b + c : ℝ) = (0) := by first | assumption | aesop | linarith
  have p2m_cond_3_gap : (0) - (a + b + c) = 0 := by linarith only [p2m_cond_3]
  have h_identity : (0) - (a * b^3 + b * c^3 + c * a^3) = ((11 / 252) : ℝ) * 1 * (((a ^ 2) + (2 * a * b)))^2 + ((2 / 63) : ℝ) * 1 * (((a ^ 2) + ((-1) * a * c)))^2 + ((1 / 14) : ℝ) * 1 * (((a ^ 2) + ((-2) * a * c)))^2 + ((1 / 36) : ℝ) * 1 * (((a ^ 2) + (2 * b * c)))^2 + ((4 / 21) : ℝ) * 1 * ((((-1) * (b ^ 2)) + (a * b)))^2 + ((4 / 63) : ℝ) * 1 * (((b ^ 2) + (2 * b * c)))^2 + ((10 / 63) : ℝ) * 1 * ((((-1) * (c ^ 2)) + (b * c)))^2 := by
    linear_combination ((((10 / 63) * (c ^ 3)) + ((11 / 63) * (a ^ 3)) + ((16 / 63) * (b ^ 3)) + ((-10 / 63) * a * (c ^ 2)) + ((10 / 21) * c * (a ^ 2)) + ((11 / 21) * b * (c ^ 2)) + ((23 / 63) * a * (b ^ 2)) + ((-23 / 63) * a * b * c))) * p2m_cond_3_gap
  have h_nonnegative : (0 : ℝ) ≤ (0) - (a * b^3 + b * c^3 + c * a^3) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
