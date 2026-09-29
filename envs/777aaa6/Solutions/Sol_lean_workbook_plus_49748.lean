-- Prove2me | solution 1 for lean_workbook_plus_49748
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:35:42.161896+00:00
-- url     : https://prove2.me/submissions/d5c24ed5-22bc-49b9-ad10-f7fe2bb33c68

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) : (3 / 2) * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) ≥ a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + a ^ 2 * d ^ 2 + b ^ 2 * c ^ 2 + b ^ 2 * d ^ 2 + c ^ 2 * d ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
