-- Prove2me | solution 1 for lean_workbook_plus_59937
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:03.152528+00:00
-- url     : https://prove2.me/submissions/591f7fc8-a61b-4d7e-af48-50a3bcd76ce5

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution : ∀ a b c d : ℝ, (a + b + c + d) ^ 2 ≥ 4 * (a + b) * (c + d) := by
  intro a b c d
  intros
  
  have h_identity : ((a + b + c + d) ^ 2) - (4 * (a + b) * (c + d)) = (1 : ℝ) * 1 * ((a + b + ((-1) * c) + ((-1) * d)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a + b + c + d) ^ 2) - (4 * (a + b) * (c + d)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
