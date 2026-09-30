-- Prove2me | solution 1 for lean_workbook_plus_29519
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T01:21:17.645528+00:00
-- url     : https://prove2.me/submissions/b4c51b0c-1ca4-4ca2-81e9-c7ca01de876f

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x^3 * y^3 + y^3 * z^3 + z^3 * x^3 >= x^3 * y^2 * z + y^3 * z^2 * x + z^3 * x^2 * y := by
  -- with p = xy, q = yz, r = zx: 3(LHS - RHS) = (p-r)²(2p+r) + (q-p)²(2q+p) + (r-q)²(2r+q)
  nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 2*(x*y) + z*x) (sq_nonneg (x*y - z*x)),
             mul_nonneg (by positivity : (0:ℝ) ≤ 2*(y*z) + x*y) (sq_nonneg (y*z - x*y)),
             mul_nonneg (by positivity : (0:ℝ) ≤ 2*(z*x) + y*z) (sq_nonneg (z*x - y*z))]
