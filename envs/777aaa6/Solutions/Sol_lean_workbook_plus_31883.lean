-- Prove2me | solution 1 for lean_workbook_plus_31883
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:56.061758+00:00
-- url     : https://prove2.me/submissions/83f6054a-804f-43ca-8fea-2fd35388bdb7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution : ∀ t : ℝ, (1 + t) ^ 2 ≥ 12 * (t - 2) := by
  intro t
  intros
  
  have h_identity : ((1 + t) ^ 2) - (12 * (t - 2)) = (25 : ℝ) * 1 * ((1 + ((-1 / 5) * t)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((1 + t) ^ 2) - (12 * (t - 2)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
