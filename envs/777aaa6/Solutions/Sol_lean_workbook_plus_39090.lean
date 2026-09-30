-- Prove2me | solution 1 for lean_workbook_plus_39090
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:41:41.470185+00:00
-- url     : https://prove2.me/submissions/bc751093-7270-42d2-85ec-253674bd8bc5

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) : (x + y + z) ^ 2 * (21 * (x ^ 2 + y ^ 2 + z ^ 2) + 946 * (x ^ 2 - y * z + y ^ 2 - z * x + z ^ 2 - x * y)) ≥ 0 := by
  apply mul_nonneg (sq_nonneg _)
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg x, sq_nonneg y, sq_nonneg z]
