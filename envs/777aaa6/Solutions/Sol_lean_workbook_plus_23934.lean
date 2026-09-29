-- Prove2me | solution 1 for lean_workbook_plus_23934
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:15:14.534551+00:00
-- url     : https://prove2.me/submissions/2f6fd575-2d59-4b12-b0ed-5cca19f13c50

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) : (a + b) ^ 2 * (b + c) ^ 2 ≥ 2 * a * b * c * (a + b + c) := by
  intros
  
  have h_identity : ((a + b) ^ 2 * (b + c) ^ 2) - (2 * a * b * c * (a + b + c)) = (1 : ℝ) * 1 * (((b ^ 2) + (a * b) + (b * c)))^2 + (1 : ℝ) * 1 * ((a * c))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a + b) ^ 2 * (b + c) ^ 2) - (2 * a * b * c * (a + b + c)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
