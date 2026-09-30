-- Prove2me | solution 1 for lean_workbook_plus_29898
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:55:40.776892+00:00
-- url     : https://prove2.me/submissions/309791b9-9d34-4805-a27e-b0a0be6d4a82

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (hx : 0 < x) : 2 * x^4 - 7 * x^3 + 12 * x + 2 > 0   := by
  by_cases htwo : x = 2
  · subst x
    norm_num
  have hp : 0 < x * (x - 2) ^ 2 :=
    mul_pos hx (sq_pos_of_ne_zero (sub_ne_zero.mpr htwo))
  have hid : 2 * x ^ 4 - 7 * x ^ 3 + 12 * x + 2 =
      2 * (x ^ 2 - 2 * x - 1) ^ 2 + x * (x - 2) ^ 2 := by ring
  nlinarith only [sq_nonneg (x ^ 2 - 2 * x - 1), hp, hid]

#print axioms solution
