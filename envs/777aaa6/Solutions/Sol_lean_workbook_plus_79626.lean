-- Prove2me | solution 1 for lean_workbook_plus_79626
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T02:17:17.017763+00:00
-- url     : https://prove2.me/submissions/667b167e-d1e9-4fc1-ae8f-98797ac72d88

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) (hx : x > 1) : 3 * x ^ 3 + 3 * x ^ 2 + 3 * x + 3 > 0 := by
  nlinarith [sq_nonneg x, sq_nonneg (x - 1)]
