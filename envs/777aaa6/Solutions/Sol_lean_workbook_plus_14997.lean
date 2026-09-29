-- Prove2me | solution 1 for lean_workbook_plus_14997
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:13:53.355997+00:00
-- url     : https://prove2.me/submissions/8ce53442-66c5-4a27-b5ed-152e801dd819

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 1 / 2 * (x + y) ^ 2 / (x * y) + 2 - 8 * (x * y) / (x + y) ^ 2 ≤ x / y + y / x := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
