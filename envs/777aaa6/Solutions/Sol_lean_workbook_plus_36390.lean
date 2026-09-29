-- Prove2me | solution 1 for lean_workbook_plus_36390
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:26.662885+00:00
-- url     : https://prove2.me/submissions/a45933a0-795a-4b45-a98a-772c013f15b3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution : ∀ a b c : ℝ, a * b * c * (a + b + c) ≥ a^3 * (b + c - a) + b^3 * (c + a - b) + c^3 * (a + b - c) := by
  intro a b c
  intros
  
  have h_identity : (a * b * c * (a + b + c)) - (a^3 * (b + c - a) + b^3 * (c + a - b) + c^3 * (a + b - c)) = (1 : ℝ) * 1 * (((a ^ 2) + ((-1 / 2) * (b ^ 2)) + ((-1 / 2) * (c ^ 2)) + (b * c) + ((-1 / 2) * a * b) + ((-1 / 2) * a * c)))^2 + ((3 / 4) : ℝ) * 1 * (((c ^ 2) + ((-1) * (b ^ 2)) + (a * b) + ((-1) * a * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (a * b * c * (a + b + c)) - (a^3 * (b + c - a) + b^3 * (c + a - b) + c^3 * (a + b - c)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
