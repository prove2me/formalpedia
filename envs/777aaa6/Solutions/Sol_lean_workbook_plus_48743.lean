-- Prove2me | solution 1 for lean_workbook_plus_48743
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:47:46.918816+00:00
-- url     : https://prove2.me/submissions/8e438cea-b0e1-4eaa-a53a-c89006515d2b

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) : 3 * (x ^ 4 * y ^ 2 + y ^ 4 * z ^ 2 + z ^ 4 * x ^ 2) * (x ^ 2 * y ^ 4 + y ^ 2 * z ^ 4 + z ^ 2 * x ^ 4) ≥ 3 * (x ^ 4 * y * z + y ^ 4 * z * x + z ^ 4 * x * y) ^ 2 := by
  nlinarith [sq_nonneg (x ^ 2 * y * (y ^ 2 * x) - y ^ 2 * z * (x ^ 2 * z)),
    sq_nonneg (x ^ 2 * y * (z ^ 2 * y) - z ^ 2 * x * (x ^ 2 * z)),
    sq_nonneg (y ^ 2 * z * (z ^ 2 * y) - z ^ 2 * x * (y ^ 2 * x))]
