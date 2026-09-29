-- Prove2me | solution 1 for lean_workbook_plus_12126
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:50:18.374005+00:00
-- url     : https://prove2.me/submissions/1e72ec8c-fb18-4387-9d16-774c3990b3e2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (habc : a * b * c = 1) : (a * b + c) * (b * c + a) * (c * a + b) ≥ (a + b) * (b + c) * (c + a) := by
  intros
  have p2m_cond_0 : (a * b * c : ℝ) = (1) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (1) - (a * b * c) = 0 := by linarith only [p2m_cond_0]
  have h_identity : ((a * b + c) * (b * c + a) * (c * a + b)) - ((a + b) * (b + c) * (c + a)) = ((1 / 2) : ℝ) * 1 * ((a + ((-1) * a * b)))^2 + ((1 / 2) : ℝ) * 1 * ((a + ((-1) * a * c)))^2 + ((1 / 2) : ℝ) * 1 * ((((-1) * b) + (a * b)))^2 + ((1 / 2) : ℝ) * 1 * ((((-1) * c) + (a * c)))^2 + ((1 / 2) : ℝ) * 1 * ((b + ((-1) * b * c)))^2 + ((1 / 2) : ℝ) * 1 * ((((-1) * c) + (b * c)))^2 := by
    linear_combination ((((-1) * (a ^ 2)) + ((-1) * (b ^ 2)) + ((-1) * (c ^ 2)) + ((-1) * a * b * c))) * p2m_cond_0_gap
  have h_nonnegative : (0 : ℝ) ≤ ((a * b + c) * (b * c + a) * (c * a + b)) - ((a + b) * (b + c) * (c + a)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
