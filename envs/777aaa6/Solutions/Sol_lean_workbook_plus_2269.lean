-- Prove2me | solution 1 for lean_workbook_plus_2269
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:22:52.993992+00:00
-- url     : https://prove2.me/submissions/e7e36193-9aee-4664-be7f-bca257e70011

import Mathlib

theorem solution (u v : ℝ) (hu : u > 0) (hv : v > 0) :
    (u + v) ^ 2 ≥ 4 * u * v := by
  nlinarith [sq_nonneg (u - v)]
