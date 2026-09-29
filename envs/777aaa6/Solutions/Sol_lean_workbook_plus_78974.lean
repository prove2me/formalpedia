-- Prove2me | solution 1 for lean_workbook_plus_78974
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:26:31.275918+00:00
-- url     : https://prove2.me/submissions/e5ecd435-4a3a-43ad-839e-91116e54e109

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : 2 * (x ^ 4 + y ^ 4 + z ^ 4) + 7 * (x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2) ≥ 3 * (x ^ 3 * y + y ^ 3 * z + z ^ 3 * x) + 3 * (x ^ 2 * y * z + y ^ 2 * z * x + z ^ 2 * x * y) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
