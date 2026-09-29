-- Prove2me | solution 1 for lean_workbook_plus_70188
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:52:47.279979+00:00
-- url     : https://prove2.me/submissions/2965cc52-b122-4bb4-908d-8306862194f3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a = 1 / 3 ∧ b = 1 / 3 ∧ c = 1 / 3) :
  a * b + b * c + c * a = 1 / 3 * 1 / 3 + 1 / 3 * 1 / 3 + 1 / 3 * 1 / 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
