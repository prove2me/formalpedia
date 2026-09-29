-- Prove2me | solution 1 for lean_workbook_plus_10489
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:40:55.023753+00:00
-- url     : https://prove2.me/submissions/0840eb43-8aae-44a8-adfb-21bc9176b647

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : 5 * (a ^ 4 + b ^ 4) + 6 * a ^ 2 * b ^ 2 ≥ 8 * (a * b ^ 3 + b * a ^ 3) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
