-- Prove2me | solution 1 for lean_workbook_plus_44743
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:14:09.779708+00:00
-- url     : https://prove2.me/submissions/04bfb2f8-c5e8-4f8a-a23a-ba2919f6b418

import Mathlib
set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (1/x + 2/y) ≥ 25 * (x + 2 * y) ^ 2 / ((x + 2 * y) ^ 3 + 48 * x * y ^ 2)   := by
  have hd : 0 < (x + 2 * y) ^ 3 + 48 * x * y ^ 2 := by positivity
  have hn : 0 ≤ 2 * (x - y) ^ 2 * (x - 2 * y) ^ 2 := by positivity
  have hid : 1 / x + 2 / y -
      25 * (x + 2 * y) ^ 2 / ((x + 2 * y) ^ 3 + 48 * x * y ^ 2) =
      2 * (x - y) ^ 2 * (x - 2 * y) ^ 2 /
        (x * y * ((x + 2 * y) ^ 3 + 48 * x * y ^ 2)) := by
    field_simp [ne_of_gt hx, ne_of_gt hy, ne_of_gt hd] <;> ring
  apply sub_nonneg.mp
  rw [hid]
  exact div_nonneg hn (by positivity)

#print axioms solution
