-- Prove2me | solution 1 for lean_workbook_plus_56363
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:22:53.681865+00:00
-- url     : https://prove2.me/submissions/b31ae965-f83a-45f3-9267-1498f88881ba

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^2 + 2*y^2 - x*y) * z^2 + (x^3 - x*y^2 - 4*x^2*y) * z + y*x^3 + y^2*x^2 ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
