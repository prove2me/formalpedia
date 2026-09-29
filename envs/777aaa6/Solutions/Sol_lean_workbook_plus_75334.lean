-- Prove2me | solution 1 for lean_workbook_plus_75334
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:39:31.253852+00:00
-- url     : https://prove2.me/submissions/cb6bd1c9-9741-40f6-a3a9-2434a8ca1314

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) (ha : a + b ≥ 0) : a^2 + 3*a + 7*b^2 + 6*b + 5*a*b ≥ -3/4 := by
  intros
  have p2m_cond_0 : (0 : ℝ) ≤ (a + b) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a + b) - (0) := by linarith only [p2m_cond_0]
  have h_identity : (a^2 + 3*a + 7*b^2 + 6*b + 5*a*b) - (-3/4) = ((3 / 4) : ℝ) * 1 * ((1 + a + (3 * b)))^2 + ((1 / 4) : ℝ) * 1 * ((a + b))^2 + ((3 / 2) : ℝ) * ((a + b) - (0)) * (1)^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (a^2 + 3*a + 7*b^2 + 6*b + 5*a*b) - (-3/4) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
