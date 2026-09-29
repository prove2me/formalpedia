-- Prove2me | solution 1 for lean_workbook_plus_18289
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:00.820743+00:00
-- url     : https://prove2.me/submissions/e4d75cd2-cc40-4d89-97f7-cf503c1344b9

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) : a^2 * b^2 + a^2 + b^2 + 2 * (a + b) + 1 ≥ 2 * (a^2 * b + a * b^2) := by
  intros
  
  have h_identity : (a^2 * b^2 + a^2 + b^2 + 2 * (a + b) + 1) - (2 * (a^2 * b + a * b^2)) = (1 : ℝ) * 1 * ((1 + a + b + ((-1) * a * b)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (a^2 * b^2 + a^2 + b^2 + 2 * (a + b) + 1) - (2 * (a^2 * b + a * b^2)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
