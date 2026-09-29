-- Prove2me | solution 1 for lean_workbook_plus_9662
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:33:33.888061+00:00
-- url     : https://prove2.me/submissions/f82b0abc-1d7a-45ca-aee7-fc09cd626f3e

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) : 7 - x^2 = 23 - 5 * x^2 ↔ x = 2 ∨ x = -2 := by
  constructor
  · intro h
    have hp : (x-2)*(x+2) = 0 := by nlinarith
    rcases mul_eq_zero.mp hp with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl|rfl) <;> norm_num
