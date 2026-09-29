-- Prove2me | solution 1 for lean_workbook_plus_30063
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:55:44.325001+00:00
-- url     : https://prove2.me/submissions/5d4f607f-b603-4bb1-88b9-e4fa1c2b237b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b + b * c + c * a = 3): a * b * c * (a + b + c) ≤ 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
