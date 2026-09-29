-- Prove2me | solution 1 for lean_workbook_plus_61744
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:19:54.143904+00:00
-- url     : https://prove2.me/submissions/13c7ba1c-ab9d-452d-a400-bf00b6e8561b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : 6 * (a ^ 2 + b ^ 2) ^ 2 + (a + b) ^ 4 ≥ 5 * (a ^ 2 + b ^ 2) * (a + b) ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
