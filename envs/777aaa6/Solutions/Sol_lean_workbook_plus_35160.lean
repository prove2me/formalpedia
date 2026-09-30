-- Prove2me | solution 1 for lean_workbook_plus_35160
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:43:29.802798+00:00
-- url     : https://prove2.me/submissions/2cc0f553-a5bd-440f-9cc2-f7a33d96b735

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x^3 * y^3 + y^3 * z^3 + z^3 * x^3 ≥ x^3 * y^2 * z + y^3 * z^2 * x + z^3 * x^2 * y := by
  have hp : 0 < x * y := mul_pos hx hy
  have hq : 0 < y * z := mul_pos hy hz
  have hr : 0 < z * x := mul_pos hz hx
  nlinarith [mul_nonneg (sq_nonneg (x*y - z*x)) (by positivity : (0:ℝ) ≤ 2*(x*y) + z*x),
             mul_nonneg (sq_nonneg (y*z - x*y)) (by positivity : (0:ℝ) ≤ 2*(y*z) + x*y),
             mul_nonneg (sq_nonneg (z*x - y*z)) (by positivity : (0:ℝ) ≤ 2*(z*x) + y*z)]
