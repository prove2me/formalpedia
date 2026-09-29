-- Prove2me | solution 1 for lean_workbook_plus_71715
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:51:31.721288+00:00
-- url     : https://prove2.me/submissions/832bc4a2-11d1-4c5b-9e6f-72adf21e0092

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x * y - x = 2) : 4 / (x + y) + 1 / y ≤ 3 / 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
