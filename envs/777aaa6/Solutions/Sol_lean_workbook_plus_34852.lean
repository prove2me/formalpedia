-- Prove2me | solution 1 for lean_workbook_plus_34852
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:17:22.650081+00:00
-- url     : https://prove2.me/submissions/d8177aa4-d27e-4f0b-8c86-3ab128b78fc0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x^2 + y^2 + z^2 + x * y * z = 4) : x^2 + y^2 + z^2 ≤ 4 + x^2 * y + y^2 * z + z^2 * x := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
