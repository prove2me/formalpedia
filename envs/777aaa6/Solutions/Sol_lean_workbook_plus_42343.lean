-- Prove2me | solution 1 for lean_workbook_plus_42343
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:45:48.013292+00:00
-- url     : https://prove2.me/submissions/38c9ef02-aba7-436f-a655-6c3c48247013

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) (hab : a * b = 1) : a ^ 2 + b ^ 2 + 4 ≥ 3 * (a + b) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2)]
