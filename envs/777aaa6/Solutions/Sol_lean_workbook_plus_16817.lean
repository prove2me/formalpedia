-- Prove2me | solution 1 for lean_workbook_plus_16817
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:21:59.36405+00:00
-- url     : https://prove2.me/submissions/e2cb8586-61da-47fb-a6d3-15d40761c511

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (hab : a + b = 7) (ha3b3 : a^3 + b^3 = 42) : 1/a + 1/b = 21/43 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
