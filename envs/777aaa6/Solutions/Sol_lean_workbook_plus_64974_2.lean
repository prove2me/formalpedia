-- Prove2me | solution 2 for lean_workbook_plus_64974
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:06:48.434056+00:00
-- url     : https://prove2.me/submissions/a672ad8e-58f2-42fa-97bb-04a9bc5724ac

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (habc : x * y * z = 1) : (x + 1) / (x ^ 2 + x + 1) + (y + 1) / (y ^ 2 + y + 1) + (z + 1) / (z ^ 2 + z + 1) ≤ 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
