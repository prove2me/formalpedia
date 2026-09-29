-- Prove2me | solution 1 for lean_workbook_plus_61206
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:32:17.400705+00:00
-- url     : https://prove2.me/submissions/859b39ec-5269-48bb-b28b-fcceea2e75ad

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hab : a > 0 ∧ b > 0 ∧ c > 0) : a * b * (a ^ 2 + b ^ 2) ≤ (a + b) ^ 4 / 8 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
