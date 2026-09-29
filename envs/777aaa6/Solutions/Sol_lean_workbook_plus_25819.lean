-- Prove2me | solution 1 for lean_workbook_plus_25819
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:35:19.539919+00:00
-- url     : https://prove2.me/submissions/77f239bb-669f-4999-b47e-deeeec73e297

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ≥ 2 * (a * b + a * c + a * d + b * c + b * d + c * d) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
