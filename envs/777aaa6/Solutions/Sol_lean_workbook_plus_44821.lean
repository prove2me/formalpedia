-- Prove2me | solution 1 for lean_workbook_plus_44821
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:14:08.446128+00:00
-- url     : https://prove2.me/submissions/a23d69b2-15a7-4579-b921-6fdf4340bdf9

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (hx : 0 < x) : x / (x^3 + 9 * x + 6) ≤ 3 / (25 * x) + 1 / 100   := by
  have hd : 0 < x ^ 3 + 9 * x + 6 := by positivity
  have hn : 0 ≤ (x - 3) ^ 2 * (x ^ 2 + 18 * x + 8) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  have hid : 3 / (25 * x) + 1 / 100 - x / (x ^ 3 + 9 * x + 6) =
      (x - 3) ^ 2 * (x ^ 2 + 18 * x + 8) /
        (100 * x * (x ^ 3 + 9 * x + 6)) := by
    field_simp [ne_of_gt hx, ne_of_gt hd] <;> ring
  apply sub_nonneg.mp
  rw [hid]
  exact div_nonneg hn (by positivity)

#print axioms solution
