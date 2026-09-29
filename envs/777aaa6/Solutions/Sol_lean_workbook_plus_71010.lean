-- Prove2me | solution 1 for lean_workbook_plus_71010
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:19:29.995046+00:00
-- url     : https://prove2.me/submissions/87ff669a-2503-4bd4-806a-778e67fb5f50

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x > -1) (y : ℝ) (hy : y = 2) : x^2 + 2*x ≥ x*y := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
