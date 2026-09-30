-- Prove2me | solution 1 for lean_workbook_plus_43612
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:13:28.770851+00:00
-- url     : https://prove2.me/submissions/f19df9b0-0fbc-413f-86e8-12935096094f

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ x : ℝ, x^4 - 6 * x^3 + 12 * x^2 - 10 * x + 3 = 0 ↔ x = 1 ∨ x = 1 ∨ x = 1 ∨ x = 3 := by
  intro x
  constructor
  · intro h
    have h1 : (x - 1)^3 * (x - 3) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h1 with h2 | h2
    · left
      have := (pow_eq_zero_iff (n := 3) (by norm_num)).mp h2
      linarith
    · right; right; right
      linarith
  · rintro (rfl | rfl | rfl | rfl) <;> norm_num
