-- Prove2me | solution 1 for lean_workbook_plus_4559
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:16:09.162722+00:00
-- url     : https://prove2.me/submissions/7ed5404e-11f3-4a7b-903c-32eb62104379

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x^3 + y^3 = x - y) : x^2 + y^2 < 1 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
