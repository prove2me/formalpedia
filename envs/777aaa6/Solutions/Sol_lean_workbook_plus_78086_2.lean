-- Prove2me | solution 2 for lean_workbook_plus_78086
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:32:35.67714+00:00
-- url     : https://prove2.me/submissions/0cc885ce-b40f-4f8f-9501-f037018370ab

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (x y : ℝ) (hy : 0 ≤ y)
    (h : y * (y + 1) ≤ (x + 1) ^ 2) : y * (y - 1) ≤ x ^ 2 := by
  by_cases ht : 0 ≤ 2 * (x - y) + 1
  · have hp := mul_nonneg ht hy
    nlinarith only [hp, sq_nonneg (x - y)]
  · have hn : 2 * (x - y) + 1 < 0 := lt_of_not_ge ht
    nlinarith only [h, hn]
