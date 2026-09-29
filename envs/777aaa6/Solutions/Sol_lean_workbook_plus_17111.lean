-- Prove2me | solution 1 for lean_workbook_plus_17111
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:49.806732+00:00
-- url     : https://prove2.me/submissions/1970281b-91b7-4fdc-b0a7-d5964eca8308

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) : a^2 * (b + c)^2 + (b^2 + c^2) * (b + c)^2 ≥ 2 * a * (b + c) * (b^2 + c^2) + 2 * b * c * (b^2 + c^2) := by
  intros
  
  have h_identity : (a^2 * (b + c)^2 + (b^2 + c^2) * (b + c)^2) - (2 * a * (b + c) * (b^2 + c^2) + 2 * b * c * (b^2 + c^2)) = (1 : ℝ) * 1 * ((((-1) * (b ^ 2)) + ((-1) * (c ^ 2)) + (a * b) + (a * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (a^2 * (b + c)^2 + (b^2 + c^2) * (b + c)^2) - (2 * a * (b + c) * (b^2 + c^2) + 2 * b * c * (b^2 + c^2)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
