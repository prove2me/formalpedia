-- Prove2me | solution 1 for lean_workbook_plus_49054
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:37:09.237691+00:00
-- url     : https://prove2.me/submissions/065cbc42-b095-4377-b4a8-1673ce412d54

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 1 / (x * y) ≥ (2 / (x + y))^2 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
