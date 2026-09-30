-- Prove2me | solution 2 for lean_workbook_plus_66911
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:14:45.452337+00:00
-- url     : https://prove2.me/submissions/3764df77-8c46-4c5a-8389-d1968e7b56c0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (habc : a * b * c = 1) (ha : a > 0) (hb : b > 0) (hc : c > 0) : a * b^2 + a * c^2 ≥ 1 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
