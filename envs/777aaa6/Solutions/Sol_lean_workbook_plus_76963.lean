-- Prove2me | solution 1 for lean_workbook_plus_76963
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:25:11.871411+00:00
-- url     : https://prove2.me/submissions/b94f2887-6201-4c03-aefa-beea818d05c1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^3 + y^3 + z^3 + x^2*y + y^2*z + z^2*x - 2*(x*y^2 + y*z^2 + z*x^2)) / (x + y) / (y + z) / (z + x) ≥ 0 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
