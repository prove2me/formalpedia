-- Prove2me | solution 1 for lean_workbook_plus_2745
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:36:54.396251+00:00
-- url     : https://prove2.me/submissions/9b6bcacf-9e55-4108-814e-bf65583d1c9f

import Mathlib

theorem solution (x y z : ℝ) :
    x ^ 6 + y ^ 6 + z ^ 6 ≥ x ^ 4 * y * z + y ^ 4 * z * x + z ^ 4 * x * y := by
  have h : 0 ≤
      (x ^ 2 - y ^ 2) ^ 2 * (x ^ 2 + y ^ 2) +
      (y ^ 2 - z ^ 2) ^ 2 * (y ^ 2 + z ^ 2) +
      (z ^ 2 - x ^ 2) ^ 2 * (z ^ 2 + x ^ 2) +
      x ^ 4 * (y - z) ^ 2 + y ^ 4 * (z - x) ^ 2 + z ^ 4 * (x - y) ^ 2 := by
    positivity
  nlinarith only [h]
