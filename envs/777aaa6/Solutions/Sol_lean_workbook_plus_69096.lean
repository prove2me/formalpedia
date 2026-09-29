-- Prove2me | solution 1 for lean_workbook_plus_69096
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:31:09.579915+00:00
-- url     : https://prove2.me/submissions/facaa5ef-22b6-47d7-8504-f95501c0ab79

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 5 * x ^ 3 * y + 5 * x * y ^ 3 ≤ 2 * x ^ 4 + 6 * x ^ 2 * y ^ 2 + 2 * y ^ 4 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
