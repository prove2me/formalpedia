-- Prove2me | solution 1 for lean_workbook_plus_27827
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:42:21.95834+00:00
-- url     : https://prove2.me/submissions/91898af3-71d8-4094-8ce8-929eb7d57893

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c d : ℝ) : Real.sqrt ((a^2 + b^2 + c^2 + d^2) / 4) ≥ (a + b + c + d) / 4 := by
  refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]
