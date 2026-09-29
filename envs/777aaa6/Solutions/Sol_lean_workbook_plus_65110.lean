-- Prove2me | solution 1 for lean_workbook_plus_65110
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:49:25.104756+00:00
-- url     : https://prove2.me/submissions/8fbcf96a-8cbd-4d08-9c05-e7e5a1edd197

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (y / x + x / y + 16 * x * y / (x + y) ^ 2) ≥ 6 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
