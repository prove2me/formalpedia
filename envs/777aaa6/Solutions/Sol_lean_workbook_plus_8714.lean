-- Prove2me | solution 1 for lean_workbook_plus_8714
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:47:31.354627+00:00
-- url     : https://prove2.me/submissions/a4ceea7b-489b-4a47-83c9-eddbfe7c60f6

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) : x^4 - x^3 + x^2 - x + 1 > 0   := by
  have hid : x^4-x^3+x^2-x+1 =
      (x^2-x/2)^2 + (3/4)*(x-2/3)^2 + 2/3 := by ring
  rw [hid]
  exact add_pos_of_nonneg_of_pos
    (add_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (sq_nonneg _)))
    (by norm_num)

#print axioms solution
