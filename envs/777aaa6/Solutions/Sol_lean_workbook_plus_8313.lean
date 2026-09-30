-- Prove2me | solution 1 for lean_workbook_plus_8313
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:13:04.444073+00:00
-- url     : https://prove2.me/submissions/099a128e-97f0-4cff-9dda-45574e6990d4

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (habc : x * y * z = 1) : (x ^ 5 * y + y ^ 5 * z + z ^ 5 * x + (x ^ 4 * y * z + y ^ 4 * z * x + z ^ 4 * x * y)) ≤ 3 * (x ^ 6 + y ^ 6 + z ^ 6) := by
  have hx4 : 0 ≤ x ^ 4 := by positivity
  have hy4 : 0 ≤ y ^ 4 := by positivity
  have hz4 : 0 ≤ z ^ 4 := by positivity
  nlinarith [mul_nonneg hx4 (sq_nonneg (x - y)), mul_nonneg hy4 (sq_nonneg (y - z)),
    mul_nonneg hz4 (sq_nonneg (z - x)),
    mul_nonneg hx4 (sq_nonneg (y - z)), mul_nonneg hy4 (sq_nonneg (z - x)),
    mul_nonneg hz4 (sq_nonneg (x - y)),
    mul_nonneg (sq_nonneg (x^2 - y^2)) (by positivity : (0:ℝ) ≤ 2*x^2 + y^2),
    mul_nonneg (sq_nonneg (y^2 - z^2)) (by positivity : (0:ℝ) ≤ 2*y^2 + z^2),
    mul_nonneg (sq_nonneg (z^2 - x^2)) (by positivity : (0:ℝ) ≤ 2*z^2 + x^2),
    mul_nonneg (sq_nonneg (x^2 - z^2)) (by positivity : (0:ℝ) ≤ 2*x^2 + z^2),
    mul_nonneg (sq_nonneg (y^2 - x^2)) (by positivity : (0:ℝ) ≤ 2*y^2 + x^2),
    mul_nonneg (sq_nonneg (z^2 - y^2)) (by positivity : (0:ℝ) ≤ 2*z^2 + y^2),
    pow_nonneg hx.le 6, pow_nonneg hy.le 6, pow_nonneg hz.le 6]
