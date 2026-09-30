-- Prove2me | solution 1 for lean_workbook_plus_67437
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:36:25.343668+00:00
-- url     : https://prove2.me/submissions/da86d3dc-d961-4e4c-b199-3996ba0ac5b2

import Mathlib

set_option autoImplicit false

theorem solution (x y z : ℝ) : x ^ 2 * y ^ 4 + z ^ 2 * x ^ 4 ≥ 2 * x ^ 3 * y ^ 2 * z := by
  nlinarith [sq_nonneg (x * y ^ 2 - z * x ^ 2)]
