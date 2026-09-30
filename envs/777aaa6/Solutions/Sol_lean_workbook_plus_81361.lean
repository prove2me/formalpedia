-- Prove2me | solution 1 for lean_workbook_plus_81361
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:14:09.757604+00:00
-- url     : https://prove2.me/submissions/26f51232-15e8-4d89-b244-7fcad3b2990a

import Mathlib

theorem solution (a b c d : ℝ) : (a + b + c + d) ^ 2 ≥ 4 * (a + d) * (b + c) := by
  nlinarith only [sq_nonneg (a + d - b - c)]
