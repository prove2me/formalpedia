-- Prove2me | solution 1 for lean_workbook_plus_42013
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:41:23.83336+00:00
-- url     : https://prove2.me/submissions/6ce4a1e2-f035-4327-8eb1-22c1d5253a6d

import Mathlib

theorem solution (a b : ℝ) :
    9 * a ^ 2 * b ^ 2 + (9 / 4) * (a + b) ^ 2 ≥ -9 * a * b * (a + b) := by
  nlinarith [sq_nonneg (3 * a * b + (3 / 2) * (a + b))]
