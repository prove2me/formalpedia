-- Prove2me | solution 1 for lean_workbook_plus_13919
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:49:18.25136+00:00
-- url     : https://prove2.me/submissions/d9a5b5d5-acdd-498c-9f97-fd570f1dcfd1

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) : x ^ 4 - x + 1 / 2 > 0   := by
  by_cases hx : x = 1 / 2
  · subst x
    norm_num
  · have hp : 0 < (x - 1 / 2) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hx)
    calc
      x ^ 4 - x + 1 / 2 = (x ^ 2 - 1 / 2) ^ 2 + (x - 1 / 2) ^ 2 := by ring
      _ > 0 := add_pos_of_nonneg_of_pos (sq_nonneg _) hp

#print axioms solution
