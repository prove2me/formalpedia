-- Prove2me | solution 1 for lean_workbook_plus_49294
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:36:42.749683+00:00
-- url     : https://prove2.me/submissions/ede2f527-d79b-4f66-8d8e-5f06ea29a333

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (h1 : a ≥ c ∧ c ≥ 0 ∧ b ≥ d ∧ d ≥ 0) (h2 : 2 * a + d = 2 * b + c) : 2 * a * b ≥ c ^ 2 + d ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
