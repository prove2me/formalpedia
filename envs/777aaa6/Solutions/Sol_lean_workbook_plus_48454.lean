-- Prove2me | solution 1 for lean_workbook_plus_48454
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:37:53.854638+00:00
-- url     : https://prove2.me/submissions/70c903ff-eef5-4e94-a063-2915c927dbd6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : (x - y) ^ 2 * (x ^ 2 + 2 * x * y + 7 * y ^ 2) + (y - z) ^ 2 * (y ^ 2 + 2 * y * z + 7 * z ^ 2) + (z - x) ^ 2 * (z ^ 2 + 2 * z * x + 7 * x ^ 2) ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
