-- Prove2me | solution 2 for lean_workbook_plus_4742
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:16:14.092803+00:00
-- url     : https://prove2.me/submissions/619826ae-a3a2-433c-beb3-1d1b319d5ea9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a * b + b * c + c * a ≤ (a + b + c) ^ 2 / 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
