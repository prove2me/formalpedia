-- Prove2me | solution 1 for lean_workbook_plus_11415
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:48:13.430206+00:00
-- url     : https://prove2.me/submissions/6159d5f6-8f8d-449d-a4cd-679e8f626b51

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (2 / (x + y) + 2 / (y + z) + 2 / (z + x)) ≥ 9 / (x + y + z) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
