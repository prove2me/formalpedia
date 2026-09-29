-- Prove2me | solution 1 for lean_workbook_plus_4441
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:07:54.224232+00:00
-- url     : https://prove2.me/submissions/5c129251-e522-4569-925a-bed4cea2f11a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) :  (a - b) * (b - c) * (c - d) * (d - a) + (a - c) ^ 2 * (b - d) ^ 2 ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
