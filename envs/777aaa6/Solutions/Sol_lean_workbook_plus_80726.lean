-- Prove2me | solution 1 for lean_workbook_plus_80726
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:01:28.121135+00:00
-- url     : https://prove2.me/submissions/2577cc7b-0ed9-4dd7-bf60-75f209993c96

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 6 * (x ^ 3 + y ^ 3 + z ^ 3) + 5 * (y * x ^ 2 + z * y ^ 2 + x * z ^ 2) ≥ 11 * (x * y ^ 2 + y * z ^ 2 + z * x ^ 2) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
