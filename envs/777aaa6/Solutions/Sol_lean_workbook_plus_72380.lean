-- Prove2me | solution 1 for lean_workbook_plus_72380
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:36:15.255016+00:00
-- url     : https://prove2.me/submissions/2d4e4b16-60f4-4a52-a1b5-185626d073e1

import Mathlib

set_option autoImplicit false

theorem solution (a e : ℝ) :
    a ^ 2 / 2 + a ^ 2 / 2 + e ^ 2 / 8 + e ^ 2 / 8 ≥ a * e := by
  nlinarith [sq_nonneg (2 * a - e)]
