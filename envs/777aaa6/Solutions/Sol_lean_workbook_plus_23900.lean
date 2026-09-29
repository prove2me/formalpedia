-- Prove2me | solution 1 for lean_workbook_plus_23900
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:50:48.799278+00:00
-- url     : https://prove2.me/submissions/b62bddb8-e443-4394-be15-59d84e1ca579

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) (h : (a + 1) * (a + b - 1) = 1) : (a^2 + 1) * (b^2 + 1) ≥ 5 / 2 := by
  intros
  have p2m_cond_0 : ((a + 1) * (a + b - 1) : ℝ) = (1) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (1) - ((a + 1) * (a + b - 1)) = 0 := by linarith only [p2m_cond_0]
  have h_identity : ((a^2 + 1) * (b^2 + 1)) - (5 / 2) = ((1 / 4) : ℝ) * 1 * ((1 + ((-2) * a * b)))^2 + ((1 / 4) : ℝ) * 1 * ((1 + ((-2) * b)))^2 := by
    linear_combination ((-1)) * p2m_cond_0_gap
  have h_nonnegative : (0 : ℝ) ≤ ((a^2 + 1) * (b^2 + 1)) - (5 / 2) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
