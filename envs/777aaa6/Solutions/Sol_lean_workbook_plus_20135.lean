-- Prove2me | solution 1 for lean_workbook_plus_20135
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:05:09.51538+00:00
-- url     : https://prove2.me/submissions/7bcdff82-9650-4f8f-8713-05ed90434042

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z) + y / (x + z) + z / (x + y)) ≥ 3 / 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
