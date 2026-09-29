-- Prove2me | solution 1 for lean_workbook_plus_6130
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:06:39.732345+00:00
-- url     : https://prove2.me/submissions/18b60309-d7f1-464c-a3bc-46819993d7d1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : 17 * (x + y + z) ^ 4 - 76 * (x + y + z) ^ 2 * (x * y + y * z + z * x) + 4 * (x + y + z) * x * y * z - 24 * (x + y + z) * (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) + 98 * (x * y + y * z + z * x) ^ 2 ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
