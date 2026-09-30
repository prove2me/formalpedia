-- Prove2me | solution 1 for lean_workbook_plus_65364
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:16:29.111291+00:00
-- url     : https://prove2.me/submissions/a8229b7d-3939-400a-932b-6dbc91d91867

import Mathlib
set_option autoImplicit false

theorem solution (a : ℝ) : (a - 1) ^ 2 * (85 * a ^ 4 - 294 * a ^ 3 + 506 * a ^ 2 - 438 * a + 213) ≥ 0   := by
  apply mul_nonneg (sq_nonneg (a - 1))
  have hid : 85 * a ^ 4 - 294 * a ^ 3 + 506 * a ^ 2 - 438 * a + 213 =
      23 * (a ^ 2 - a) ^ 2 + 62 * (a - 1) ^ 4 +
        95 * (a - 1) ^ 2 + 16 * a ^ 2 + 56 := by ring
  rw [hid]
  positivity

#print axioms solution
