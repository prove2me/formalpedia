-- Prove2me | solution 1 for lean_workbook_plus_30631
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:12.788524+00:00
-- url     : https://prove2.me/submissions/bb56f4aa-211f-4f71-893b-131bdcf9c153

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c d : ℝ) (h : a + b + c + d = 6) : a * b + b * c + c * d + d * a ≤ 9 := by
  intros
  have p2m_cond_0 : (a + b + c + d : ℝ) = (6) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (6) - (a + b + c + d) = 0 := by linarith only [p2m_cond_0]
  have h_identity : (9) - (a * b + b * c + c * d + d * a) = ((1 / 4) : ℝ) * 1 * ((a + c + ((-1) * b) + ((-1) * d)))^2 := by
    linear_combination (((3 / 2) + ((1 / 4) * a) + ((1 / 4) * b) + ((1 / 4) * c) + ((1 / 4) * d))) * p2m_cond_0_gap
  have h_nonnegative : (0 : ℝ) ≤ (9) - (a * b + b * c + c * d + d * a) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
