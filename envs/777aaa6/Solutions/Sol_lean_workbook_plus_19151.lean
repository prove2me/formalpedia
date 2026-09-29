-- Prove2me | solution 1 for lean_workbook_plus_19151
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:47:09.40099+00:00
-- url     : https://prove2.me/submissions/0af3f61b-2c06-40d7-ba9e-f23a3dda462d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (habc : a * b * c = 1) :
  (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a + 1) * (b + 1) * (c + 1) := by
  intros
  have p2m_cond_0 : (a * b * c : ℝ) = (1) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (1) - (a * b * c) = 0 := by linarith only [p2m_cond_0]
  have h_identity : ((a^2 + 1) * (b^2 + 1) * (c^2 + 1)) - ((a + 1) * (b + 1) * (c + 1)) = ((1 / 2) : ℝ) * 1 * ((a + ((-1) * b)))^2 + ((1 / 2) : ℝ) * 1 * ((a + ((-1) * c)))^2 + ((1 / 2) : ℝ) * 1 * (((a * b) + ((-1) * a * c)))^2 + ((1 / 2) : ℝ) * 1 * (((a * b) + ((-1) * b * c)))^2 + ((1 / 2) : ℝ) * 1 * (((a * c) + ((-1) * b * c)))^2 + ((1 / 2) : ℝ) * 1 * ((b + ((-1) * c)))^2 := by
    linear_combination ((((-1) * a) + ((-1) * b) + ((-1) * c) + ((-1) * a * b * c))) * p2m_cond_0_gap
  have h_nonnegative : (0 : ℝ) ≤ ((a^2 + 1) * (b^2 + 1) * (c^2 + 1)) - ((a + 1) * (b + 1) * (c + 1)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
