-- Prove2me | solution 1 for lean_workbook_plus_65989
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:36:14.591674+00:00
-- url     : https://prove2.me/submissions/e01464bc-7d4c-4d95-8f4f-9e7e11b13a1c

import Mathlib

theorem solution : ∀ x : ℝ, x^4 + 2*x^3 + 3*x^2 + 3*x + 2 ≥
    (x^2+x)^2 + 2*(|x|-1)^2 := by
  intro x
  nlinarith only [sq_abs x, abs_nonneg x, neg_le_abs x]

theorem equality_iff (x : ℝ) :
    x^4 + 2*x^3 + 3*x^2 + 3*x + 2 = (x^2+x)^2 + 2*(|x|-1)^2 ↔ x = 0 := by
  constructor
  · intro h
    have hz : |x| = 0 := by nlinarith only [h, sq_abs x, abs_nonneg x, neg_le_abs x]
    exact abs_eq_zero.mp hz
  · rintro rfl
    simp
