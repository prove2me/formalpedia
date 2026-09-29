-- Prove2me | solution 1 for lean_workbook_plus_26222
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:26:15.80564+00:00
-- url     : https://prove2.me/submissions/d4faf5bb-6be9-4aac-979b-600d9d63efa5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a + b) ^ 2 + (b + c) ^ 2 + (c + a) ^ 2 ≥ (2 * (a + b + c)) ^ 2 / 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
