-- Prove2me | solution 1 for lean_workbook_plus_23167
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:54:53.435522+00:00
-- url     : https://prove2.me/submissions/a3490f9d-67d9-45a0-923f-46fe2a026bb8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x^2*y + y^2*z + z^2*x + (x*y^2 + y*z^2 + z*x^2) ≥ 6*x*y*z := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
