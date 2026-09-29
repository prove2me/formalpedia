-- Prove2me | solution 1 for lean_workbook_plus_17333
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:13:45.15037+00:00
-- url     : https://prove2.me/submissions/8384e993-8741-4d7d-8bac-9d71d8341307

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a ^ 2 + b ^ 2 + c ^ 2 ≥ (a + b + c) ^ 2 / 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
