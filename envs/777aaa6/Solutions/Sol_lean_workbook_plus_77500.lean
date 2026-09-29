-- Prove2me | solution 1 for lean_workbook_plus_77500
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:02:18.693924+00:00
-- url     : https://prove2.me/submissions/9d4f4802-bfff-49c0-b69b-650f9b6d63a6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h1 : a > 0 ∧ b > 0 ∧ c > 0) (hab : a * b + b * c + c * a = 3): a * b * c * (a + b + c) ≤ 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
