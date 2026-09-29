-- Prove2me | solution 1 for lean_workbook_plus_2281
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:15:08.284483+00:00
-- url     : https://prove2.me/submissions/39344e15-ad42-45ac-a2c9-e394586d9bc1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) (h₁ : b ≥ a) : b^3 - 12*b + 16 ≥ a^3 - 12*a - 16 := by
  intros
  have p2m_cond_0 : (a : ℝ) ≤ (b) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (b) - (a) := by linarith only [p2m_cond_0]
  have h_identity : (b^3 - 12*b + 16) - (a^3 - 12*a - 16) = (32 : ℝ) * 1 * ((1 + ((-1 / 4) * b) + ((1 / 4) * a)))^2 + (4 : ℝ) * ((b) - (a)) * ((1 + ((-1 / 4) * b) + ((1 / 4) * a)))^2 + ((3 / 4) : ℝ) * ((b) - (a)) * ((a + b))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (b^3 - 12*b + 16) - (a^3 - 12*a - 16) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
