-- Prove2me | solution 1 for lean_workbook_plus_57543
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:15:36.909262+00:00
-- url     : https://prove2.me/submissions/68a91340-03ec-4b05-b7c5-556258b7dd5c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t ≤ 3/2) : t * (t - 3) ^ 2 - 4 ≤ 0 := by
  intros
  have p2m_cond_1 : (t : ℝ) ≤ (3/2) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (3/2) - (t) := by linarith only [p2m_cond_1]
  have h_identity : (0) - (t * (t - 3) ^ 2 - 4) = ((5 / 2) : ℝ) * 1 * ((1 + ((-1) * t)))^2 + (1 : ℝ) * ((3/2) - (t)) * ((1 + ((-1) * t)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (0) - (t * (t - 3) ^ 2 - 4) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
