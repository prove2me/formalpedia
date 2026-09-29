-- Prove2me | solution 1 for lean_workbook_plus_55470
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:59:06.076231+00:00
-- url     : https://prove2.me/submissions/27fa3fa9-214f-4b70-9ebe-277e17ecbbea

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ) : x^2 + 6*x + 5 = 0 ↔ x = -5 ∨ x = -1 := by
  constructor
  · intro h
    have hp : (x+5)*(x+1)=0 := by nlinarith
    rcases mul_eq_zero.mp hp with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num
