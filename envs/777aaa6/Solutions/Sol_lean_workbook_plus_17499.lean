-- Prove2me | solution 1 for lean_workbook_plus_17499
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:13:17.826978+00:00
-- url     : https://prove2.me/submissions/14fb7844-93ec-4fb4-a094-e669d79d5c60

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
