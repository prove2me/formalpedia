-- Prove2me | solution 1 for lean_workbook_plus_15838
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:12:49.629347+00:00
-- url     : https://prove2.me/submissions/8fdaaa92-bca7-4da7-b5c4-2b7cfb7d14b8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ a * b + b * c + c * d + d * a := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
