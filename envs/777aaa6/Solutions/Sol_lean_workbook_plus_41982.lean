-- Prove2me | solution 1 for lean_workbook_plus_41982
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:29:39.835981+00:00
-- url     : https://prove2.me/submissions/cf010f5f-2709-4406-bc50-ca15637d8c21

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 3 * (x ^ 4 + y ^ 4 + z ^ 4) + 15 * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2) ≥ 6 * (x ^ 3 * y + y ^ 3 * z + z ^ 3 * x) + 6 * (x * y ^ 3 + y * z ^ 3 + z * x ^ 3) + 6 * (x ^ 2 * y * z + y ^ 2 * z * x + z ^ 2 * x * y) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
