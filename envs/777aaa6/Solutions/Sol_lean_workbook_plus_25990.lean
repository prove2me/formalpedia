-- Prove2me | solution 1 for lean_workbook_plus_25990
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:35:07.896419+00:00
-- url     : https://prove2.me/submissions/a8f5eeb7-f12a-46f1-af58-769e7cc5a941

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x * y * z = 1) : 1 / (x^2 + x + 1) + 1 / (y^2 + y + 1) + 1 / (z^2 + z + 1) >= 1 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
