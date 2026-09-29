-- Prove2me | solution 1 for lean_workbook_plus_7314
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:05:56.644855+00:00
-- url     : https://prove2.me/submissions/8b0b9f74-ee20-4ecb-9308-4d8f5e06de4a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x^3 + y^3 = x - y) (h : x^2 + 4*y^2 < 1) : x^2 + 5*y^2 > 4*x*y := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
