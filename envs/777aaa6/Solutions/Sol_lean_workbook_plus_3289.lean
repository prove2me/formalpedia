-- Prove2me | solution 1 for lean_workbook_plus_3289
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:14:48.070891+00:00
-- url     : https://prove2.me/submissions/28992bfb-9f9f-4bf4-b91d-980d9d2b26cc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x^2*y + y*z^2 + y^2*x + z*y^2 + x^2*z + z^2*x >= 6*x*y*z := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
