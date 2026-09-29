-- Prove2me | solution 1 for lean_workbook_plus_20844
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:36:55.689375+00:00
-- url     : https://prove2.me/submissions/973e8fdd-768d-43e1-9db8-8d768b199816

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x ^ 3 + y ^ 3 + z ^ 3 ≥ x ^ 2 * y + y ^ 2 * z + z ^ 2 * x := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
