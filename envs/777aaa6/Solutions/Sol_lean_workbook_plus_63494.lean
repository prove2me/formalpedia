-- Prove2me | solution 1 for lean_workbook_plus_63494
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:10:28.590696+00:00
-- url     : https://prove2.me/submissions/1e053055-64ef-47b1-a8bc-90e49a6f7810

import Mathlib
set_option autoImplicit false

theorem solution (a : ℝ) (ha : a > 0) (hab : a^3 = 6 * (a + 1)) : ¬ ∃ x : ℝ, x^2 + a * x + a^2 - 6 = 0   := by
  have ha2 : 8 < a ^ 2 := by
    by_contra! hle
    have hm := mul_le_mul_of_nonneg_right hle ha.le
    have ha3 : 3 ≤ a := by nlinarith [hm]
    nlinarith [sq_nonneg (a - 3)]
  rintro ⟨x, hx⟩
  nlinarith [sq_nonneg (2 * x + a)]

#print axioms solution
