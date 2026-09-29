-- Prove2me | solution 1 for lean_workbook_plus_35509
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:40.505635+00:00
-- url     : https://prove2.me/submissions/77a0b336-34c4-4e2b-bcfc-bf7aed328518

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c d : ℝ) : (b * d * (a + c) + a * c * (b + d))^2 ≤ 2 * b^2 * d^2 * (a + c)^2 + 2 * a^2 * c^2 * (b + d)^2 := by
  intros
  
  have h_identity : (2 * b^2 * d^2 * (a + c)^2 + 2 * a^2 * c^2 * (b + d)^2) - ((b * d * (a + c) + a * c * (b + d))^2) = (1 : ℝ) * 1 * (((a * b * c) + (a * c * d) + ((-1) * a * b * d) + ((-1) * b * c * d)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (2 * b^2 * d^2 * (a + c)^2 + 2 * a^2 * c^2 * (b + d)^2) - ((b * d * (a + c) + a * c * (b + d))^2) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
