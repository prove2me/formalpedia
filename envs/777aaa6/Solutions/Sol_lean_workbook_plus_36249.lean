-- Prove2me | solution 1 for lean_workbook_plus_36249
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:04:54.510217+00:00
-- url     : https://prove2.me/submissions/0a23d4d1-47f8-44c0-86d3-7b3d8a91199b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (z - y) / (x + 2 * y) + (x - z) / (y + 2 * z) + (y - x) / (z + 2 * x) ≥ 0 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
