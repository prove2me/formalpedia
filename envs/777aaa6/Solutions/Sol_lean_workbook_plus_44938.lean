-- Prove2me | solution 1 for lean_workbook_plus_44938
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:25:56.454713+00:00
-- url     : https://prove2.me/submissions/efb97ca8-6333-401d-8e1e-6fc9c724ed84

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 8 * (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 ≥ 9 * (x ^ 2 + y * z) * (y ^ 2 + z * x) * (z ^ 2 + x * y) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    sq_nonneg (x + y - z), sq_nonneg (y + z - x), sq_nonneg (z + x - y),
    mul_pos hx hy, mul_pos hy hz, mul_pos hz hx,
    mul_pos (mul_pos hx hy) hz,
    sq_nonneg (x^2 - y^2), sq_nonneg (y^2 - z^2), sq_nonneg (z^2 - x^2),
    sq_nonneg (x^2 - y*z), sq_nonneg (y^2 - z*x), sq_nonneg (z^2 - x*y),
    sq_nonneg (x*y - y*z), sq_nonneg (y*z - z*x), sq_nonneg (z*x - x*y)]
