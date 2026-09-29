-- Prove2me | solution 1 for lean_workbook_plus_27267
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:21.204716+00:00
-- url     : https://prove2.me/submissions/08852259-8beb-4481-86da-98534d2642fa

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) : (a - b) ^ 2 * (a ^ 2 + 4 * b ^ 2) * (a ^ 2 + 2 * a * b + 2 * b ^ 2) ≥ 0 := by
  intros
  
  have h_identity : ((a - b) ^ 2 * (a ^ 2 + 4 * b ^ 2) * (a ^ 2 + 2 * a * b + 2 * b ^ 2)) - (0) = (1 : ℝ) * 1 * ((((-2) * (b ^ 3)) + (a * (b ^ 2)) + (b * (a ^ 2))))^2 + (1 : ℝ) * 1 * (((a ^ 3) + ((-2) * (b ^ 3)) + (a * (b ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a - b) ^ 2 * (a ^ 2 + 4 * b ^ 2) * (a ^ 2 + 2 * a * b + 2 * b ^ 2)) - (0) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
