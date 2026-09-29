-- Prove2me | solution 1 for lean_workbook_plus_54225
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:48:39.671192+00:00
-- url     : https://prove2.me/submissions/fb9f7e67-6f0c-42d9-938f-2775be96e2d7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ) : x^2 - 5*x - 4 ≤ 10 ↔ -2 ≤ x ∧ x ≤ 7 := by
  constructor
  · intro h
    constructor
    · by_contra hn
      nlinarith [mul_pos_of_neg_of_neg (show x+2 < 0 by linarith) (show x-7 < 0 by linarith)]
    · by_contra hn
      nlinarith [mul_pos (show 0 < x+2 by linarith) (show 0 < x-7 by linarith)]
  · rintro ⟨hl, hu⟩
    nlinarith [mul_nonneg (show 0 ≤ x+2 by linarith) (show 0 ≤ 7-x by linarith)]
