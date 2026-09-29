-- Prove2me | solution 1 for lean_workbook_plus_74209
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:51:44.778863+00:00
-- url     : https://prove2.me/submissions/91bcefa3-ed19-449f-bb15-039218263f48

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a + b + c = 3) : a^2 + b^2 + c^2 + a * b + a * c + b * c ≥ 6 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
