-- Prove2me | solution 1 for lean_workbook_plus_65230
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:50:07.476018+00:00
-- url     : https://prove2.me/submissions/0caf1245-1e0f-4163-afe3-e03a91e590a7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a + b + c) ^ 2 / 3 ≥ a * b + b * c + c * a := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
