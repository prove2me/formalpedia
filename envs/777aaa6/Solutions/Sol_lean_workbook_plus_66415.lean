-- Prove2me | solution 1 for lean_workbook_plus_66415
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:32:21.16238+00:00
-- url     : https://prove2.me/submissions/b7c903ed-1f92-4897-b32c-7206c82ebd0d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x^3 + y^3 = x - y) : 4 * x^2 - 5 * y^2 < 5 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
