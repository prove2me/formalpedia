-- Prove2me | solution 1 for lean_workbook_plus_58233
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:48:26.671547+00:00
-- url     : https://prove2.me/submissions/02b69522-2808-41de-85e4-afc25b2b3e05

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ) : x^2 - 6*x + 8 > 3 ↔ x > 5 ∨ x < 1 := by
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    nlinarith [mul_nonneg (show 0 ≤ 5-x by linarith) (show 0 ≤ x-1 by linarith)]
  · rintro (h | h)
    · nlinarith [mul_pos (show 0 < x-5 by linarith) (show 0 < x-1 by linarith)]
    · nlinarith [mul_pos_of_neg_of_neg (show x-5 < 0 by linarith) (show x-1 < 0 by linarith)]
