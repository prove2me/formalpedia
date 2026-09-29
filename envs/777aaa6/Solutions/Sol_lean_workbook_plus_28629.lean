-- Prove2me | solution 1 for lean_workbook_plus_28629
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:53:53.852953+00:00
-- url     : https://prove2.me/submissions/5ddd1837-b897-4816-980e-7f9d1c6cc8cd

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) : (a - b) ^ 4 * (a ^ 2 + a * b + b ^ 2) ≥ 0 := by
  intros
  
  have h_identity : ((a - b) ^ 4 * (a ^ 2 + a * b + b ^ 2)) - (0) = (3 : ℝ) * 1 * ((((-1 / 2) * (a ^ 3)) + (b * (a ^ 2)) + ((-1 / 2) * a * (b ^ 2))))^2 + ((1 / 4) : ℝ) * 1 * (((a ^ 3) + (2 * (b ^ 3)) + ((-3) * a * (b ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a - b) ^ 4 * (a ^ 2 + a * b + b ^ 2)) - (0) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
