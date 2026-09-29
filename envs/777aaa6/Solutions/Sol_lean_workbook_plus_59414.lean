-- Prove2me | solution 1 for lean_workbook_plus_59414
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:01:40.519957+00:00
-- url     : https://prove2.me/submissions/1ea99b54-1ad5-4bff-b499-f57852a972b2

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (k : ℝ) : 2 * k - 3 = 1 / 4 * k ^ 2 ↔ k = 2 ∨ k = 6 := by
  constructor
  · intro h
    have hp : (k-2)*(k-6)=0 := by nlinarith
    rcases mul_eq_zero.mp hp with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num
