-- Prove2me | solution 1 for lean_workbook_plus_29666
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:02:26.610845+00:00
-- url     : https://prove2.me/submissions/a9200c66-0635-4392-9e12-58de143266e2

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ) : 2 * x^2 - 5 * x + 2 = 0 ↔ x = 2 ∨ x = 1/2 := by
  constructor
  · intro h
    have hp : (x-2)*(2*x-1)=0 := by nlinarith
    rcases mul_eq_zero.mp hp with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num
