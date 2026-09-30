-- Prove2me | solution 1 for lean_workbook_plus_19905
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:13:29.750145+00:00
-- url     : https://prove2.me/submissions/859a119e-a267-42de-8856-848e5a6d4760

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x^4 + y^4 + z^4 + x*y*z*(x + y + z) ≥ (2/3)*(x*y + y*z + z*x)^2 := by
  nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (y^2 - z^2), sq_nonneg (z^2 - x^2), sq_nonneg (x*y - y*z), sq_nonneg (y*z - z*x), sq_nonneg (z*x - x*y)]
