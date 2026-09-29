-- Prove2me | solution 1 for lean_workbook_plus_81150
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:37:09.974581+00:00
-- url     : https://prove2.me/submissions/1d9bc0d7-bbb1-49f4-b326-ba06f8801650

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h1 : a * b < c ^ 2) (h2 : b * c < a ^ 2) (h3 : a * c < b ^ 2) : a * b + b * c + c * a < 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
