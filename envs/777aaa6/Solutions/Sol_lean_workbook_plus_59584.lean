-- Prove2me | solution 1 for lean_workbook_plus_59584
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:34:08.777904+00:00
-- url     : https://prove2.me/submissions/80e4134e-fb8c-45ad-81e4-be498b2b3f8b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (x + y) + y / (y + z) + z / (z + x)) ≤ 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
