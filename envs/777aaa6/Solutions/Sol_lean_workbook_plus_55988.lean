-- Prove2me | solution 1 for lean_workbook_plus_55988
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:22:16.605579+00:00
-- url     : https://prove2.me/submissions/169d37e3-cb8c-4003-8e74-7ab28201e63d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (h1 : a + b + c + d >= 4) (h2 : a * b * c * d >= 1) : (a + b + c + d) ^ 2 + 48 * a * b * c * d >= 64 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
