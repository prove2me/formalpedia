-- Prove2me | solution 1 for lean_workbook_plus_61700
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:19:57.108446+00:00
-- url     : https://prove2.me/submissions/03962b7a-28bc-44d5-85ee-8ce0c6154156

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (hab : a + b = 7) (hab3 : a^3 + b^3 = 42) : 1/a + 1/b = 21/43 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
