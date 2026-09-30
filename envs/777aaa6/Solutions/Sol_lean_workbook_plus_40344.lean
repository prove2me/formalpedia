-- Prove2me | solution 1 for lean_workbook_plus_40344
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:27:06.354844+00:00
-- url     : https://prove2.me/submissions/b1f9540d-95d3-49e9-baf4-03df895171c5

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (hab : a + b + c = 0)
    (hbc : abs a + abs b + abs c = 1) : a + b / 2 + c / 3 ≤ 1 / 3 := by
  linarith [le_abs_self a, neg_le_abs b, neg_le_abs c, abs_nonneg b]
