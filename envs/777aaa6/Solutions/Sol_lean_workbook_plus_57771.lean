-- Prove2me | solution 1 for lean_workbook_plus_57771
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:48:36.960317+00:00
-- url     : https://prove2.me/submissions/6d68415b-3242-4fc2-a5fa-f1508b171cb2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ) : 2 * x ^ 2 + 3 * x > 0 ↔ x < -3 / 2 ∨ x > 0 := by
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    nlinarith [mul_nonneg (show 0 ≤ 2*x+3 by linarith) (show 0 ≤ -x by linarith)]
  · rintro (h | h)
    · nlinarith [mul_pos_of_neg_of_neg (show x < 0 by linarith) (show 2*x+3 < 0 by linarith)]
    · nlinarith [mul_pos h (show 0 < 2*x+3 by linarith)]
