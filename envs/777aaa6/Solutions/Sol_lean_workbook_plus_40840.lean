-- Prove2me | solution 1 for lean_workbook_plus_40840
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:06:26.741178+00:00
-- url     : https://prove2.me/submissions/921f842d-1bc7-4ffd-97e9-520684263bfa

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x : ℝ) (h : x ≥ 1) : x^3 - 5 * x^2 + 8 * x - 4 ≥ 0 := by
  intros
  have p2m_cond_0 : (1 : ℝ) ≤ (x) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (x) - (1) := by linarith only [p2m_cond_0]
  have h_identity : (x^3 - 5 * x^2 + 8 * x - 4) - (0) = (4 : ℝ) * ((x) - (1)) * ((1 + ((-1 / 2) * x)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (x^3 - 5 * x^2 + 8 * x - 4) - (0) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
