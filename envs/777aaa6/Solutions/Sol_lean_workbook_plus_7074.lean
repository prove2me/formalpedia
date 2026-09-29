-- Prove2me | solution 1 for lean_workbook_plus_7074
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:59:16.254643+00:00
-- url     : https://prove2.me/submissions/b0f5c9a8-2db1-4093-bbd9-477fb758f5c2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) : a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 + a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * d ^ 2 + d ^ 2 * a ^ 2 ≥ 2 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * d + a * d ^ 3) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
