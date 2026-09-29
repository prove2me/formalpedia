-- Prove2me | solution 1 for lean_workbook_plus_62920
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:18:03.723289+00:00
-- url     : https://prove2.me/submissions/5d96e072-5cd3-404e-9cde-a26474e8e836

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x / y / z + y / z / x + z / x / y ≥ 1 / x + 1 / y + 1 / z := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
