-- Prove2me | solution 1 for lean_workbook_plus_68253
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:14:10.028973+00:00
-- url     : https://prove2.me/submissions/843fa7c6-58f0-4066-b034-269c5014beb2

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) : 5 * x ^ 4 + x ^ 2 + 2 > 5 * x := by
  nlinarith [sq_nonneg (x ^ 2 - 1 / 3), sq_nonneg (26 * x - 15), sq_nonneg (x - 15 / 26)]
