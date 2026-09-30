-- Prove2me | solution 1 for lean_workbook_plus_690
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:47:49.905102+00:00
-- url     : https://prove2.me/submissions/4ff48c2d-4ba5-4ada-b89d-a3aee6951810

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : x^3*y + y^3*z + z^3*x + x*y^3 + y*z^3 + z*x^3 >= 2 * (x^2*y^2 + y^2*z^2 + z^2*x^2) := by
  nlinarith [mul_nonneg (mul_pos hx hy).le (sq_nonneg (x - y)),
    mul_nonneg (mul_pos hy hz).le (sq_nonneg (y - z)),
    mul_nonneg (mul_pos hz hx).le (sq_nonneg (z - x))]
