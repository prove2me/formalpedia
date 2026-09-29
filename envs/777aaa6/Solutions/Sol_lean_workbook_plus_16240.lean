-- Prove2me | solution 1 for lean_workbook_plus_16240
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:21:00.440978+00:00
-- url     : https://prove2.me/submissions/c2c13853-0eaf-4e30-8542-f1c1ed9b21cb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y) / (2 * z + x + y) + (y + z) / (2 * x + y + z) + (z + x) / (2 * y + z + x) ≥ 3 / 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
