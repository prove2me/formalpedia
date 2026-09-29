-- Prove2me | solution 1 for lean_workbook_plus_49238
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:30:44.797542+00:00
-- url     : https://prove2.me/submissions/6467d7a7-b5cc-4091-b76f-e0c963d15364

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution : ∀ a b c : ℝ, (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) ≥ (1/2)*((a + b) * (b + c) * (c + a) - 4 * a * b * c)^2 := by
  intro a b c
  intros
  
  have h_identity : ((a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2)) - ((1/2)*((a + b) * (b + c) * (c + a) - 4 * a * b * c)^2) = ((1 / 2) : ℝ) * 1 * (((a * (c ^ 2)) + (b * (a ^ 2)) + (c * (b ^ 2)) + ((-1) * a * (b ^ 2)) + ((-1) * b * (c ^ 2)) + ((-1) * c * (a ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2)) - ((1/2)*((a + b) * (b + c) * (c + a) - 4 * a * b * c)^2) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
