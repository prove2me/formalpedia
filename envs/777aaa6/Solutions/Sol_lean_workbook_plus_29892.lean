-- Prove2me | solution 1 for lean_workbook_plus_29892
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:55:50.57029+00:00
-- url     : https://prove2.me/submissions/7ebe371c-dd71-4968-9aea-db42abef93c5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hab : x * (x + y + z) = 3 * y * z) : (x + y) ^ 3 + (x + z) ^ 3 ≤ 2 * (z + y) ^ 3 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
