-- Prove2me | solution 1 for lean_workbook_plus_26014
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:26:36.788441+00:00
-- url     : https://prove2.me/submissions/4f12f535-f926-4d32-8b07-70011a254a63

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^2*y + x^2*z - 2*x*y*z) + (y^2*z + y^2*x - 2*y*z*x) + (z^2*x + z^2*y - 2*z*x*y) ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
