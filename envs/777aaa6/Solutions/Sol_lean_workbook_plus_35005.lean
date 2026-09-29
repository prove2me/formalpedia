-- Prove2me | solution 1 for lean_workbook_plus_35005
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:47:20.121829+00:00
-- url     : https://prove2.me/submissions/1dc1f264-ae99-4aa3-8514-7498d062ea7c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y : ℝ) (hx : x^2 + y^2 = 9) : x^2 + 3*y^2 + 4*x ≤ 29 := by
  intros
  have p2m_cond_0 : (x^2 + y^2 : ℝ) = (9) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (9) - (x^2 + y^2) = 0 := by linarith only [p2m_cond_0]
  have h_identity : (29) - (x^2 + 3*y^2 + 4*x) = (2 : ℝ) * 1 * ((1 + ((-1) * x)))^2 := by
    linear_combination (3) * p2m_cond_0_gap
  have h_nonnegative : (0 : ℝ) ≤ (29) - (x^2 + 3*y^2 + 4*x) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
