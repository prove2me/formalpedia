-- Prove2me | solution 1 for lean_workbook_plus_62276
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:18:51.570333+00:00
-- url     : https://prove2.me/submissions/4a54c8b3-75d8-4269-9807-5e24fa7f6fcf

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (h1 : a ≥ b ∧ b ≥ 0) (h2 : c ≥ d ∧ d ≥ 0) (h3 : a ≤ c) (h4 : a * b ≤ c * d) : a + b ≤ c + d := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
