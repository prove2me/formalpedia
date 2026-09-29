-- Prove2me | solution 1 for lean_workbook_plus_29714
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:04:09.619564+00:00
-- url     : https://prove2.me/submissions/0cf52c86-b1be-4f7d-8a05-a67d59028c06

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1) : (1 + 1 / x) * (1 + 1 / y) ≥ 9 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
