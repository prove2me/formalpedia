-- Prove2me | solution 1 for lean_workbook_plus_75631
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:49:42.195061+00:00
-- url     : https://prove2.me/submissions/47eac126-d645-48b4-9182-b7c7f2620953

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a : ℝ) (h : a ≥ 1) : 4 * a ^ 3 - 9 * a ^ 2 + 9 * a + 4 ≥ 0 := by
  intros
  have p2m_cond_0 : (1 : ℝ) ≤ (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (1) := by linarith only [p2m_cond_0]
  have h_identity : (4 * a ^ 3 - 9 * a ^ 2 + 9 * a + 4) - (0) = ((28 / 5) : ℝ) * 1 * (1)^2 + ((3 / 5) : ℝ) * 1 * ((1 + a))^2 + ((8 / 5) : ℝ) * ((a) - (1)) * ((1 + ((-1) * a)))^2 + ((3 / 5) : ℝ) * ((a) - (1)) * ((1 + ((-2) * a)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (4 * a ^ 3 - 9 * a ^ 2 + 9 * a + 4) - (0) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
