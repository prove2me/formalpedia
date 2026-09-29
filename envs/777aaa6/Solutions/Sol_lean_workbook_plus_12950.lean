-- Prove2me | solution 1 for lean_workbook_plus_12950
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:51:20.758206+00:00
-- url     : https://prove2.me/submissions/ab47f81d-4abe-474d-8f59-fd7628cc688a

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ) : x * (x^2 + 8 * x + 16) * (4 - x) = 0 ↔ x = 0 ∨ x = -4 ∨ x = 4 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl h
      · right; left
        nlinarith [sq_nonneg (x+4)]
    · right; right; linarith
  · rintro (rfl | rfl | rfl) <;> norm_num
