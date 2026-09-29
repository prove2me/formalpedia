-- Prove2me | solution 1 for lean_workbook_plus_51285
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:19:02.890285+00:00
-- url     : https://prove2.me/submissions/50526fef-5295-4817-a697-fe15c017d90a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d e : ℝ) (h1 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) (h2 : a + b + c + d + e = 1) : a * d + d * c + c * b + b * e + e * a ≤ 1 / 5 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
