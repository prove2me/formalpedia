-- Prove2me | solution 1 for lean_workbook_plus_16622
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:14:14.670656+00:00
-- url     : https://prove2.me/submissions/e1675040-c95c-447d-8aa2-e287dafdbba0

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + a * c) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
