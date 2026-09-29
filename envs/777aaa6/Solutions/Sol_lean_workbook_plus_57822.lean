-- Prove2me | solution 1 for lean_workbook_plus_57822
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:51:42.839305+00:00
-- url     : https://prove2.me/submissions/3001c3b2-b4a9-4c99-b561-b2f86c7d337d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (y : ℝ) (hy : y ≥ 1/2) : 64*y^3 + 8*y + 28 ≥ 100*y^2 := by
  intros
  have p2m_cond_0 : (1/2 : ℝ) ≤ (y) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (y) - (1/2) := by linarith only [p2m_cond_0]
  have h_identity : (64*y^3 + 8*y + 28) - (100*y^2) = (60 : ℝ) * 1 * ((1 + ((-1) * y)))^2 + (64 : ℝ) * ((y) - (1/2)) * ((1 + ((-1) * y)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (64*y^3 + 8*y + 28) - (100*y^2) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
