-- Prove2me | solution 1 for lean_workbook_plus_10366
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:52:47.38392+00:00
-- url     : https://prove2.me/submissions/9a89cead-52fa-4aa4-87db-060e16f59252

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) (ha : a ≥ 0 ∧ b ≥ 0 ∧ a + b = 2) : a^4 + b^4 ≥ 2 := by
  intros
  have p2m_cond_2 : (a + b : ℝ) = (2) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (2) - (a + b) = 0 := by linarith only [p2m_cond_2]
  have h_identity : (a^4 + b^4) - (2) = ((1 / 4) : ℝ) * 1 * (((a ^ 2) + ((-1) * a * b)))^2 + ((5 / 8) : ℝ) * 1 * (((a ^ 2) + ((-1) * (b ^ 2))))^2 + ((1 / 4) : ℝ) * 1 * ((((-1) * (b ^ 2)) + (a * b)))^2 := by
    linear_combination (((-1) + ((-1 / 2) * a) + ((-1 / 2) * b) + ((-1 / 4) * (a ^ 2)) + ((-1 / 4) * (b ^ 2)) + ((-1 / 8) * (a ^ 3)) + ((-1 / 8) * (b ^ 3)) + ((-3 / 8) * a * (b ^ 2)) + ((-3 / 8) * b * (a ^ 2)) + ((-1 / 2) * a * b))) * p2m_cond_2_gap
  have h_nonnegative : (0 : ℝ) ≤ (a^4 + b^4) - (2) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
