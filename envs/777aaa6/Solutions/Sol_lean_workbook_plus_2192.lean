-- Prove2me | solution 1 for lean_workbook_plus_2192
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:24:35.298163+00:00
-- url     : https://prove2.me/submissions/c35fc030-175c-4c6f-b700-7bb15ce49d7e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) + a * b ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
