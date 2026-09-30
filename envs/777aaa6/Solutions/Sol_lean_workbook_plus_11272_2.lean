-- Prove2me | solution 2 for lean_workbook_plus_11272
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:51:26.804849+00:00
-- url     : https://prove2.me/submissions/10be8043-21ea-44d2-a604-0e166eb77792

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (hab : a + b + c = 3) : a^2 + b^2 + a^2 * b^2 + a * b * c ≥ 4 * a * b := by
  intros
  have p2m_cond_0 : (a + b + c : ℝ) = (3) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (3) - (a + b + c) = 0 := by linarith only [p2m_cond_0]
  have h_identity : (a^2 + b^2 + a^2 * b^2 + a * b * c) - (4 * a * b) = ((1 / 2) : ℝ) * 1 * ((a + ((-1) * a * b)))^2 + ((1 / 2) : ℝ) * 1 * ((a + ((-1) * b)))^2 + ((1 / 2) : ℝ) * 1 * ((((-1) * b) + (a * b)))^2 := by
    linear_combination (((-1) * a * b)) * p2m_cond_0_gap
  have h_nonnegative : (0 : ℝ) ≤ (a^2 + b^2 + a^2 * b^2 + a * b * c) - (4 * a * b) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
