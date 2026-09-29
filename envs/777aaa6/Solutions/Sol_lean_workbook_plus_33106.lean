-- Prove2me | solution 1 for lean_workbook_plus_33106
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:15:17.191076+00:00
-- url     : https://prove2.me/submissions/2f7daeab-623d-440c-b54d-f717c727157b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution : ∀ a b c : ℝ, (a^2 + b^2)^2 + c^2 * (a + b)^2 ≥ 2 * c * (a^2 + b^2) * (a + b) := by
  intro a b c
  intros
  
  have h_identity : ((a^2 + b^2)^2 + c^2 * (a + b)^2) - (2 * c * (a^2 + b^2) * (a + b)) = (1 : ℝ) * 1 * (((a ^ 2) + (b ^ 2) + ((-1) * a * c) + ((-1) * b * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a^2 + b^2)^2 + c^2 * (a + b)^2) - (2 * c * (a^2 + b^2) * (a + b)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
