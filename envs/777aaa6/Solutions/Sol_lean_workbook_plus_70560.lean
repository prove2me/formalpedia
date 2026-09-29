-- Prove2me | solution 1 for lean_workbook_plus_70560
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:51:26.755386+00:00
-- url     : https://prove2.me/submissions/34e75305-4c2e-4277-853f-c2c7e366b01c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (x / y) + (y / x) ≥ 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
