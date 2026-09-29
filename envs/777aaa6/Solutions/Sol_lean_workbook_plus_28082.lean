-- Prove2me | solution 1 for lean_workbook_plus_28082
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:05:58.579806+00:00
-- url     : https://prove2.me/submissions/7d5c0d0f-b154-4202-8228-bca5560ead3b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 3 * (a + b + c) ^ 2 ≥ a ^ 2 + b ^ 2 + c ^ 2 + 8 * (a * b + b * c + c * a) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
