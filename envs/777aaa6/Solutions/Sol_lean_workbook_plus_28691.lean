-- Prove2me | solution 1 for lean_workbook_plus_28691
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:05:23.161413+00:00
-- url     : https://prove2.me/submissions/304c2101-9aee-4c1e-9db2-b2dcc23f2641

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ)
  (h₀ : a + b + c = 7 - d)
  (h₁ : a^2 + b^2 + c^2 = 13 - d^2) :
  3 * (a^2 + b^2 + c^2) ≥ (a + b + c)^2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
