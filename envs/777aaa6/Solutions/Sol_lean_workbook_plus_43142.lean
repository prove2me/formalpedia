-- Prove2me | solution 1 for lean_workbook_plus_43142
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:16:09.642182+00:00
-- url     : https://prove2.me/submissions/88281db3-0ca3-476e-884b-ad64dfc23343

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x^3 + y^3 = x - y) : x^2 + y^2 < 1 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
