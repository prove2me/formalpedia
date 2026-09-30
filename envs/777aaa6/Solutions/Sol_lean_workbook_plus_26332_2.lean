-- Prove2me | solution 2 for lean_workbook_plus_26332
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:26:03.17291+00:00
-- url     : https://prove2.me/submissions/5e881d0e-4612-41ac-9d7e-cf4828c9e948

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) : (7 / 16) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 ≥ d ^ 2 * a ^ 2 + c ^ 2 * a ^ 2 + a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * d ^ 2 + b ^ 2 * d ^ 2 + a * b * c * d := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
