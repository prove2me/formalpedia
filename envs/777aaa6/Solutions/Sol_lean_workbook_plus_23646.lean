-- Prove2me | solution 1 for lean_workbook_plus_23646
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:23.357119+00:00
-- url     : https://prove2.me/submissions/0471f49e-37be-4489-8908-d0b42370ed00

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (h : a + b + c = 0) : (2 * a ^ 2 + b * c) * (2 * b ^ 2 + c * a) * (2 * c ^ 2 + a * b) ≤ 0 := by
  intros
  have p2m_cond_0 : (a + b + c : ℝ) = (0) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0) - (a + b + c) = 0 := by linarith only [p2m_cond_0]
  have h_identity : (0) - ((2 * a ^ 2 + b * c) * (2 * b ^ 2 + c * a) * (2 * c ^ 2 + a * b)) = (1 : ℝ) * 1 * (((a * (c ^ 2)) + (b * (a ^ 2)) + (c * (b ^ 2)) + ((-1) * a * (b ^ 2)) + ((-1) * b * (c ^ 2)) + ((-1) * c * (a ^ 2))))^2 := by
    linear_combination ((((a ^ 2) * (b ^ 3)) + ((a ^ 2) * (c ^ 3)) + ((a ^ 3) * (b ^ 2)) + ((a ^ 3) * (c ^ 2)) + ((b ^ 2) * (c ^ 3)) + ((b ^ 3) * (c ^ 2)) + (a * (b ^ 2) * (c ^ 2)) + (b * (a ^ 2) * (c ^ 2)) + (c * (a ^ 2) * (b ^ 2)))) * p2m_cond_0_gap
  have h_nonnegative : (0 : ℝ) ≤ (0) - ((2 * a ^ 2 + b * c) * (2 * b ^ 2 + c * a) * (2 * c ^ 2 + a * b)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
