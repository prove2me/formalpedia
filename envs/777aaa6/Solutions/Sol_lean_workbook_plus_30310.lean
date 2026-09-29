-- Prove2me | solution 1 for lean_workbook_plus_30310
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:55:10.6478+00:00
-- url     : https://prove2.me/submissions/bb81c180-f7d1-4a19-bafc-c221584a6dd7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : 9 = 3 * (a ^ 2 + b ^ 2 + c ^ 2)) :
  a + b + c ≤ 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
