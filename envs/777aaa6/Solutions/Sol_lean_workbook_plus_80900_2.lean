-- Prove2me | solution 2 for lean_workbook_plus_80900
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:36:10.62355+00:00
-- url     : https://prove2.me/submissions/eb7b9eec-f261-4a12-810d-aedd3d97f98d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (h1 : a ≥ b ∧ b ≥ c ∧ c ≥ d) (h2 : a + b + c + d = 2) : a^2 + 2 * b * c + d^2 ≥ 1 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
