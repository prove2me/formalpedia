-- Prove2me | solution 1 for lean_workbook_plus_27233
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:48:07.12054+00:00
-- url     : https://prove2.me/submissions/b49d2d79-99d6-4d40-841a-d232de92740a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (hab : 0 < a) (hbc : 0 < b) (hca : 0 < c) (habc : a * b + b * c + c * a = 1) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ 4 / 3 := by
  intros
  have p2m_cond_3 : (a * b + b * c + c * a : ℝ) = (1) := by first | assumption | aesop | linarith
  have p2m_cond_3_gap : (1) - (a * b + b * c + c * a) = 0 := by linarith only [p2m_cond_3]
  have h_identity : ((a^2 + 1) * (b^2 + 1) * (c^2 + 1)) - (4 / 3) = ((41 / 384) : ℝ) * 1 * ((a + (2 * a * b)))^2 + ((41 / 384) : ℝ) * 1 * ((a + ((-2) * a * b)))^2 + ((199 / 1920) : ℝ) * 1 * ((a + (2 * a * b * c)))^2 + ((199 / 1920) : ℝ) * 1 * ((a + ((-2) * a * b * c)))^2 + ((1 / 8) : ℝ) * 1 * ((a + (2 * a * c)))^2 + ((1 / 8) : ℝ) * 1 * ((a + ((-2) * a * c)))^2 + ((1 / 12) : ℝ) * 1 * ((a + ((-2) * b)))^2 + ((19 / 480) : ℝ) * 1 * ((a + (2 * b * c)))^2 + ((19 / 480) : ℝ) * 1 * ((a + ((-2) * b * c)))^2 + ((1 / 24) : ℝ) * 1 * ((a + (2 * c)))^2 + ((1 / 8) : ℝ) * 1 * ((a + ((-2) * c)))^2 + ((7 / 96) : ℝ) * 1 * (((2 * b) + (a * b)))^2 + ((7 / 96) : ℝ) * 1 * ((((-2) * b) + (a * b)))^2 + ((41 / 480) : ℝ) * 1 * (((2 * b * c) + (a * b * c)))^2 + ((41 / 480) : ℝ) * 1 * ((((-2) * b * c) + (a * b * c)))^2 + ((1 / 12) : ℝ) * 1 * ((b + ((-2) * c)))^2 := by
    linear_combination ((-1 / 3)) * p2m_cond_3_gap
  have h_nonnegative : (0 : ℝ) ≤ ((a^2 + 1) * (b^2 + 1) * (c^2 + 1)) - (4 / 3) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
