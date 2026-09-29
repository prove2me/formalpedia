-- Prove2me | solution 1 for lean_workbook_plus_70074
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:52:54.896914+00:00
-- url     : https://prove2.me/submissions/f41245d8-46a9-4a8c-9186-7430722c7d84

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : 3 * a ^ 4 - 4 * a ^ 3 * b + b ^ 4 ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
