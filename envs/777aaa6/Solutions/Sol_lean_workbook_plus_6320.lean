-- Prove2me | solution 1 for lean_workbook_plus_6320
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:28.955273+00:00
-- url     : https://prove2.me/submissions/9cd3d5d1-4c11-477e-ac17-9cf765b7de25

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution :
  ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → a + b > c ∧ a + c > b ∧ b + c > a → a^2 * (a - b) * (a - c) + b^2 * (b - a) * (b - c) + c^2 * (c - a) * (c - b) ≥ 0 := by
  intro a b c
  intros
  
  have h_identity : (a^2 * (a - b) * (a - c) + b^2 * (b - a) * (b - c) + c^2 * (c - a) * (c - b)) - (0) = (1 : ℝ) * 1 * (((a ^ 2) + ((-1 / 2) * (b ^ 2)) + ((-1 / 2) * (c ^ 2)) + (b * c) + ((-1 / 2) * a * b) + ((-1 / 2) * a * c)))^2 + ((3 / 4) : ℝ) * 1 * (((c ^ 2) + ((-1) * (b ^ 2)) + (a * b) + ((-1) * a * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (a^2 * (a - b) * (a - c) + b^2 * (b - a) * (b - c) + c^2 * (c - a) * (c - b)) - (0) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
