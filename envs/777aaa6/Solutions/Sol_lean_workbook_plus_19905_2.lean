-- Prove2me | solution 2 for lean_workbook_plus_19905
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:04:51.932113+00:00
-- url     : https://prove2.me/submissions/ce1b33e1-8505-4e83-94a5-6c42037ab4fd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x^4 + y^4 + z^4 + x*y*z*(x + y + z) ≥ (2/3)*(x*y + y*z + z*x)^2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
