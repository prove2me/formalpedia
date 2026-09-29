-- Prove2me | solution 1 for lean_workbook_plus_11871
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:50:39.814717+00:00
-- url     : https://prove2.me/submissions/6dd553cd-c2be-488c-bc10-fd7edc6d7a1a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (h : a * b * c = 0) :
  a ^ 2 * b ^ 4 + b ^ 2 * c ^ 4 + c ^ 2 * a ^ 4 + a ^ 3 * b * c ^ 2 + b ^ 3 * c * a ^ 2 + c ^ 3 * a * b ^ 2 ≥
  2 * (a ^ 3 * b ^ 2 * c + b ^ 3 * c ^ 2 * a + c ^ 3 * a ^ 2 * b) := by
  intros
  have p2m_cond_0 : (a * b * c : ℝ) = (0) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0) - (a * b * c) = 0 := by linarith only [p2m_cond_0]
  have h_identity : (a ^ 2 * b ^ 4 + b ^ 2 * c ^ 4 + c ^ 2 * a ^ 4 + a ^ 3 * b * c ^ 2 + b ^ 3 * c * a ^ 2 + c ^ 3 * a * b ^ 2) - (2 * (a ^ 3 * b ^ 2 * c + b ^ 3 * c ^ 2 * a + c ^ 3 * a ^ 2 * b)) = ((1 / 4) : ℝ) * 1 * (((c * (a ^ 2)) + ((-2) * a * (b ^ 2))))^2 + ((2 / 3) : ℝ) * 1 * (((c * (a ^ 2)) + ((-1) * b * (c ^ 2))))^2 + ((1 / 12) : ℝ) * 1 * (((c * (a ^ 2)) + ((-2) * b * (c ^ 2))))^2 := by
    linear_combination (((b * (a ^ 2)) + ((-1) * a * (b ^ 2)) + ((-1) * b * (c ^ 2)) + ((-1) * c * (a ^ 2)) + (2 * c * (b ^ 2)) + ((1 / 3) * a * (c ^ 2)))) * p2m_cond_0_gap
  have h_nonnegative : (0 : ℝ) ≤ (a ^ 2 * b ^ 4 + b ^ 2 * c ^ 4 + c ^ 2 * a ^ 4 + a ^ 3 * b * c ^ 2 + b ^ 3 * c * a ^ 2 + c ^ 3 * a * b ^ 2) - (2 * (a ^ 3 * b ^ 2 * c + b ^ 3 * c ^ 2 * a + c ^ 3 * a ^ 2 * b)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
