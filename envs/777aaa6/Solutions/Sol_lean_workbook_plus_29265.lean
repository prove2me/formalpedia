-- Prove2me | solution 1 for lean_workbook_plus_29265
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:25:37.009376+00:00
-- url     : https://prove2.me/submissions/55bebb3a-f2eb-44d0-b743-1722adf15ec7

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) : x^4 + 6 * x^3 + 35 * x^2 + 6 * x + 1 > 0   := by
  have hid : x^4 + 6*x^3 + 35*x^2 + 6*x + 1 =
      (x^2 + 3*x)^2 + 26*(x + 3/26)^2 + 17/26 := by ring
  rw [hid]
  exact add_pos_of_nonneg_of_pos
    (add_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (sq_nonneg _)))
    (by norm_num)

#print axioms solution
