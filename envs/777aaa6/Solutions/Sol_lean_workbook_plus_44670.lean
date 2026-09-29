-- Prove2me | solution 1 for lean_workbook_plus_44670
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:16:49.992862+00:00
-- url     : https://prove2.me/submissions/5138a089-6ac4-4cc9-af2e-3265c6878c9f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) : a * b * (c ^ 2 + d ^ 2) + c * d * (a ^ 2 + b ^ 2) ≤ (a + b) ^ 2 * (c + d) ^ 2 / 4 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
