-- Prove2me | solution 2 for lean_workbook_plus_29255
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:53:28.860763+00:00
-- url     : https://prove2.me/submissions/e732ba93-460c-4308-93b7-5c50ca746ff8

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x1 x2 x3 : ℝ) (hx1 : 0 < x1) (hx2 : 0 < x2) (hx3 : 0 < x3) (hx : x1 + x2 + x3 = 1) : x1 * x2 + x1 * x3 + x2 * x3 ≤ 1 / 3 := by
  intros
  have p2m_cond_3 : (x1 + x2 + x3 : ℝ) = (1) := by first | assumption | aesop | linarith
  have p2m_cond_3_gap : (1) - (x1 + x2 + x3) = 0 := by linarith only [p2m_cond_3]
  have h_identity : (1 / 3) - (x1 * x2 + x1 * x3 + x2 * x3) = ((1 / 6) : ℝ) * 1 * ((x1 + ((-1) * x2)))^2 + ((1 / 6) : ℝ) * 1 * ((x1 + ((-1) * x3)))^2 + ((1 / 6) : ℝ) * 1 * ((x2 + ((-1) * x3)))^2 := by
    linear_combination (((1 / 3) + ((1 / 3) * x1) + ((1 / 3) * x2) + ((1 / 3) * x3))) * p2m_cond_3_gap
  have h_nonnegative : (0 : ℝ) ≤ (1 / 3) - (x1 * x2 + x1 * x3 + x2 * x3) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
