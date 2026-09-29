-- Prove2me | solution 1 for lean_workbook_plus_3522
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:48:48.648129+00:00
-- url     : https://prove2.me/submissions/14e246e6-6bd4-4690-8756-7968fa298c87

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a^2 + b^2 + c^2 = 3 → a * b + b * c + c * a ≤ 3 := by
  intro a b c
  intros
  have p2m_cond_3 : (a^2 + b^2 + c^2 : ℝ) = (3) := by first | assumption | aesop | linarith
  have p2m_cond_3_gap : (3) - (a^2 + b^2 + c^2) = 0 := by linarith only [p2m_cond_3]
  have h_identity : (3) - (a * b + b * c + c * a) = ((1 / 2) : ℝ) * 1 * ((a + ((-1) * b)))^2 + ((1 / 2) : ℝ) * 1 * ((a + ((-1) * c)))^2 + ((1 / 2) : ℝ) * 1 * ((b + ((-1) * c)))^2 := by
    linear_combination (1) * p2m_cond_3_gap
  have h_nonnegative : (0 : ℝ) ≤ (3) - (a * b + b * c + c * a) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
