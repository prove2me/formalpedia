-- Prove2me | solution 1 for lean_workbook_plus_2620
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:30:42.954645+00:00
-- url     : https://prove2.me/submissions/74fa2302-2822-43bb-af94-929b4c32d2d7

import Mathlib

theorem solution (a b : ℝ) :
    (a ^ 2 + 2) * (b ^ 2 + 2) ≥ 3 * ((a + b) ^ 2 / 2 + 1) := by
  nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a - b)]
