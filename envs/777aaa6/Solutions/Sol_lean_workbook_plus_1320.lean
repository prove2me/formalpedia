-- Prove2me | solution 1 for lean_workbook_plus_1320
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:23:46.696168+00:00
-- url     : https://prove2.me/submissions/da96b4c8-1117-4d79-a97c-66eddd09530b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) : 2 * (a + c) ^ 2 + 2 * (b + d) ^ 2 ≥ 8 * (a * c + b * d) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
