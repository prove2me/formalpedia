-- Prove2me | solution 1 for lean_workbook_plus_12962
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:30:20.251907+00:00
-- url     : https://prove2.me/submissions/11d01fcf-90cc-4958-b30a-b7a115005494

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (b : ℝ) (hb : b ≤ 3) :
  125 * b * (3 - b) + (3 - b) ^ 2 * (125 * b + 525 / 2) / 4 ≤ 666 := by
  intros
  have p2m_cond_0 : (b : ℝ) ≤ (3) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (3) - (b) := by linarith only [p2m_cond_0]
  have h_identity : (666) - (125 * b * (3 - b) + (3 - b) ^ 2 * (125 * b + 525 / 2) / 4) = ((333 / 8) : ℝ) * 1 * ((1 + ((-5 / 3) * b)))^2 + ((45 / 4) : ℝ) * ((3) - (b)) * ((1 + ((-5 / 3) * b)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (666) - (125 * b * (3 - b) + (3 - b) ^ 2 * (125 * b + 525 / 2) / 4) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
