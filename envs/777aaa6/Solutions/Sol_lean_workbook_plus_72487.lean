-- Prove2me | solution 1 for lean_workbook_plus_72487
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:36:12.777322+00:00
-- url     : https://prove2.me/submissions/256a4b44-a1c0-47ee-94e5-0b5462300eb7

import Mathlib

set_option autoImplicit false

theorem solution (a : ℝ) (ha : 0 < a) : a ^ 3 + 2 ≥ 3 * a := by
  nlinarith [mul_nonneg (sq_nonneg (a - 1)) (show 0 ≤ a + 2 by linarith)]
