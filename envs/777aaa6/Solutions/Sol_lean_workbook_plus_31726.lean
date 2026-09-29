-- Prove2me | solution 1 for lean_workbook_plus_31726
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:49:18.191082+00:00
-- url     : https://prove2.me/submissions/ef0041d2-0608-49cb-ac62-37a54ae1171d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a : ℝ) (h : 1 ≤ a) : a^5 + a^4 + a^3 + a^2 + a + 1 ≥ 2 * (a^2 + a + 1) := by
  intros
  have p2m_cond_0 : (1 : ℝ) ≤ (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (1) := by linarith only [p2m_cond_0]
  have h_identity : (a^5 + a^4 + a^3 + a^2 + a + 1) - (2 * (a^2 + a + 1)) = ((1 / 2) : ℝ) * ((a) - (1)) * ((1 + a))^2 + ((1 / 6) : ℝ) * ((a) - (1)) * ((1 + ((-1) * a)))^2 + ((1 / 3) : ℝ) * ((a) - (1)) * ((1 + (2 * a)))^2 + (1 : ℝ) * ((a) - (1)) * ((a + (a ^ 2)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (a^5 + a^4 + a^3 + a^2 + a + 1) - (2 * (a^2 + a + 1)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
