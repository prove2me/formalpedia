-- Prove2me | solution 1 for lean_workbook_plus_78086
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:24:47.764474+00:00
-- url     : https://prove2.me/submissions/f17eeb1c-ae2e-45e7-9ccb-5d94a837c15a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hy : 0 ≤ y) (h : y * (y + 1) ≤ (x + 1) ^ 2) : y * (y - 1) ≤ x ^ 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
