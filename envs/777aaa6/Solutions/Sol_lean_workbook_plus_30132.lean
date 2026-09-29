-- Prove2me | solution 1 for lean_workbook_plus_30132
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:55:34.289978+00:00
-- url     : https://prove2.me/submissions/e4cc07b2-4b17-46d6-8b34-95290ee10b0b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d: ℝ) (h: a + b + c + d = 1) :
  a^2 + b^2 + c^2 + d^2 >= 1 / 4 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
