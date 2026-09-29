-- Prove2me | solution 1 for lean_workbook_plus_26084
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:54.371433+00:00
-- url     : https://prove2.me/submissions/4a11741c-2cd4-458d-870d-d692947de34e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) : (a - b + b - c) ^ 2 ≥ 4 * (a - b) * (b - c) := by
  intros
  
  have h_identity : ((a - b + b - c) ^ 2) - (4 * (a - b) * (b - c)) = (1 : ℝ) * 1 * ((a + c + ((-2) * b)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a - b + b - c) ^ 2) - (4 * (a - b) * (b - c)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
