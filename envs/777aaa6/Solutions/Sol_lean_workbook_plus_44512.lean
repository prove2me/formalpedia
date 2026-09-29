-- Prove2me | solution 1 for lean_workbook_plus_44512
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:27:47.008527+00:00
-- url     : https://prove2.me/submissions/4517490b-be9d-41de-ad5a-2d7065929a0b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a^2 + b^2 + c^2) * 3 ≥ (a + b + c)^2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
