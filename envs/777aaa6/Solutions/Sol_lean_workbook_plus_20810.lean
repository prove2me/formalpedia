-- Prove2me | solution 1 for lean_workbook_plus_20810
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:30:48.178046+00:00
-- url     : https://prove2.me/submissions/40ae185f-46bf-40d6-a996-da00d162d2f9

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution : ∀ a b c : ℝ, 4 * (a * b + b * c + c * a) * (b ^ 2 + b * c + c ^ 2) ≤ (b + c) ^ 2 * (a + b + c) ^ 2 := by
  intro a b c
  intros
  
  have h_identity : ((b + c) ^ 2 * (a + b + c) ^ 2) - (4 * (a * b + b * c + c * a) * (b ^ 2 + b * c + c ^ 2)) = (1 : ℝ) * 1 * ((((-1) * (b ^ 2)) + ((-1) * (c ^ 2)) + (a * b) + (a * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((b + c) ^ 2 * (a + b + c) ^ 2) - (4 * (a * b + b * c + c * a) * (b ^ 2 + b * c + c ^ 2)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
