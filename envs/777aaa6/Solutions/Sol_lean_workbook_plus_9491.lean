-- Prove2me | solution 1 for lean_workbook_plus_9491
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:30:50.88816+00:00
-- url     : https://prove2.me/submissions/259a0879-6c88-4914-9bf1-28721bec8ddf

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) : (a^2 + b^2 + c^2)^2 - 2 * a * b * c * (a + b + c) ≥ 2 * (a + b + c) * (a - b) * (b - c) * (a - c) := by
  intros
  
  have h_identity : ((a^2 + b^2 + c^2)^2 - 2 * a * b * c * (a + b + c)) - (2 * (a + b + c) * (a - b) * (b - c) * (a - c)) = (1 : ℝ) * 1 * (((a ^ 2) + (a * c) + ((-1) * a * b)))^2 + (1 : ℝ) * 1 * (((b ^ 2) + (a * b) + ((-1) * b * c)))^2 + (1 : ℝ) * 1 * ((((-1) * (c ^ 2)) + (a * c) + ((-1) * b * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a^2 + b^2 + c^2)^2 - 2 * a * b * c * (a + b + c)) - (2 * (a + b + c) * (a - b) * (b - c) * (a - c)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
