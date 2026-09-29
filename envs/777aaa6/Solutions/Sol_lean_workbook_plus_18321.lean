-- Prove2me | solution 1 for lean_workbook_plus_18321
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:51:19.127959+00:00
-- url     : https://prove2.me/submissions/49616600-8711-4b79-8b01-5b1abbf27886

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y : ℝ) (h : x + y ≥ 0) : x ^ 5 + y ^ 5 ≥ x * y * (x ^ 3 + y ^ 3) := by
  intros
  have p2m_cond_0 : (0 : ℝ) ≤ (x + y) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (x + y) - (0) := by linarith only [p2m_cond_0]
  have h_identity : (x ^ 5 + y ^ 5) - (x * y * (x ^ 3 + y ^ 3)) = (1 : ℝ) * ((x + y) - (0)) * (((x ^ 2) + ((-1) * x * y)))^2 + (1 : ℝ) * ((x + y) - (0)) * ((((-1) * (y ^ 2)) + (x * y)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (x ^ 5 + y ^ 5) - (x * y * (x ^ 3 + y ^ 3)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
