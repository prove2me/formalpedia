-- Prove2me | solution 1 for lean_workbook_plus_63556
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:10:27.775549+00:00
-- url     : https://prove2.me/submissions/e05ba422-5e2b-4536-b99b-12d41840cd60

import Mathlib
set_option autoImplicit false

theorem solution (x y : ℝ) (h : x^3 / 3 + x^2 / 2 + x = y^3 / 3 + y^2 / 2 + y) : x = y   := by
  have hq : 0 < 2 * (x ^ 2 + x * y + y ^ 2) + 3 * (x + y) + 6 := by
    nlinarith [sq_nonneg (x + y + 1), sq_nonneg (x - y)]
  have he : (x - y) * (2 * (x ^ 2 + x * y + y ^ 2) + 3 * (x + y) + 6) = 0 := by
    nlinarith [h]
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (ne_of_gt hq))

#print axioms solution
