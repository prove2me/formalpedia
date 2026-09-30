-- Prove2me | solution 2 for lean_workbook_plus_75055
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:53:00.939074+00:00
-- url     : https://prove2.me/submissions/cac8274e-4a75-4d9e-bceb-03b87de6372b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : 3 * (x + y) ≥ 2 * (x * y + 1)) : x ^ 2 + y ^ 2 ≥ 2 / 7 * (x ^ 2 * y ^ 2 + 1) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
