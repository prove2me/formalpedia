-- Prove2me | solution 1 for lean_workbook_plus_49641
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:41:23.056105+00:00
-- url     : https://prove2.me/submissions/0e910bc8-6366-4bcf-ab0e-9a13e45b9252

import Mathlib

theorem solution (x y z : ℝ) :
    (x * z) ^ 2 + (y * x) ^ 2 + (z * y) ^ 2 ≥ x * y * z * (x + y + z) := by
  nlinarith [sq_nonneg (x * z - y * x), sq_nonneg (y * x - z * y),
    sq_nonneg (z * y - x * z)]
