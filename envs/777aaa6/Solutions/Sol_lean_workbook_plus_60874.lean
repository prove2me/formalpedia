-- Prove2me | solution 1 for lean_workbook_plus_60874
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:40:20.814705+00:00
-- url     : https://prove2.me/submissions/8e759990-d8c2-4a1f-8459-f492658d3c33

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) : x^2 + 3*x - 54 = 0 ↔ x = -9 ∨ x = 6 := by
  constructor
  · intro h
    have h' : (x + 9) * (x - 6) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h1 | h1
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num
