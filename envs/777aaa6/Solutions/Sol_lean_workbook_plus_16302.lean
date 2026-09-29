-- Prove2me | solution 1 for lean_workbook_plus_16302
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:21:05.677642+00:00
-- url     : https://prove2.me/submissions/55974c18-b8ef-4830-b23d-282b4ea6d83a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y + z) / x + 2 ≥ 4 * (z / (z + x) + y / (x + y)) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
