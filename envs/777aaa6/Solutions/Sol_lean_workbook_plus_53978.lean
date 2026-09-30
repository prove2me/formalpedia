-- Prove2me | solution 1 for lean_workbook_plus_53978
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:27:05.52244+00:00
-- url     : https://prove2.me/submissions/77274432-f883-414d-8e0c-505cc376f1ee

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) :
    10 / 3 ≤ |a - 1| + |b - 2| + |c - 3| + |3 * a + 2 * b + c| := by
  linarith [neg_le_abs (a - 1), neg_le_abs (b - 2), neg_le_abs (c - 3),
    le_abs_self (3 * a + 2 * b + c), abs_nonneg (b - 2), abs_nonneg (c - 3),
    abs_nonneg (3 * a + 2 * b + c)]
