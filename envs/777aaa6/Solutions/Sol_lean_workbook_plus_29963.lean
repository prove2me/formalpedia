-- Prove2me | solution 1 for lean_workbook_plus_29963
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:11:25.770793+00:00
-- url     : https://prove2.me/submissions/27a179b9-c0e3-45ac-aa99-068f914b6e55

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) : x * y * z * (y * z ^ 2 + x ^ 2 * z + x * y ^ 2) + z ^ 4 * x ^ 2 + y ^ 2 * x ^ 4 + y ^ 4 * z ^ 2 ≥ 2 / 3 * (x ^ 2 * y + z * y ^ 2 + z ^ 2 * x) ^ 2 := by
  nlinarith [sq_nonneg (x ^ 2 * y - y ^ 2 * z), sq_nonneg (y ^ 2 * z - z ^ 2 * x), sq_nonneg (z ^ 2 * x - x ^ 2 * y)]
