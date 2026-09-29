-- Prove2me | solution 1 for lean_workbook_plus_81292
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:37:30.635806+00:00
-- url     : https://prove2.me/submissions/7aca96f9-a09e-442f-a47f-7d2a1f980dab

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hab : a > 0 ∧ b > 0 ∧ c > 0) (h : a^2 + b^2 - a * b = c^2) : (a - c) * (b - c) ≤ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
