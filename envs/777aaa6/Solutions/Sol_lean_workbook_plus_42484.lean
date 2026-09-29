-- Prove2me | solution 1 for lean_workbook_plus_42484
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:17:16.19451+00:00
-- url     : https://prove2.me/submissions/6db27310-2936-4dd9-bee2-75c1d35dcbb2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a + b + c = 1) : 1 - (a ^ 2 + b ^ 2 + c ^ 2) ≤ 3 / 4 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
