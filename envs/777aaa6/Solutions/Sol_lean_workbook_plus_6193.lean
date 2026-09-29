-- Prove2me | solution 1 for lean_workbook_plus_6193
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:30:36.777772+00:00
-- url     : https://prove2.me/submissions/05550405-f5a1-4a63-89f0-bd829212f2a7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ): a^2 + a * b + b^2 ≥ 3 * (a + b - 1) := by
  intros
  
  have h_identity : (a^2 + a * b + b^2) - (3 * (a + b - 1)) = (3 : ℝ) * 1 * ((1 + ((-1 / 2) * a) + ((-1 / 2) * b)))^2 + ((1 / 4) : ℝ) * 1 * ((a + ((-1) * b)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (a^2 + a * b + b^2) - (3 * (a + b - 1)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
