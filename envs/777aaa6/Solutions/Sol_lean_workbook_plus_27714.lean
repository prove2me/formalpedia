-- Prove2me | solution 1 for lean_workbook_plus_27714
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:14:10.086605+00:00
-- url     : https://prove2.me/submissions/6347353a-3033-4d2d-8468-c8b811196301

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : 1 < x) : x^3 - x^2 + x - 1 > 0 := by
  (intros; nlinarith [sq_nonneg (x)])
