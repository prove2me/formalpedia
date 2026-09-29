-- Prove2me | solution 1 for lean_workbook_plus_60186
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:33:03.111392+00:00
-- url     : https://prove2.me/submissions/09156607-db11-49f2-9b47-1f1a0f4e7ed2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (y / x + x / y + (x * y) / (x + y) ^ 2) ≥ 9 / 4 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
