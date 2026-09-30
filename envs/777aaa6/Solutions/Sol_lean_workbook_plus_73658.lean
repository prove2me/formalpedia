-- Prove2me | solution 1 for lean_workbook_plus_73658
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:42:15.835103+00:00
-- url     : https://prove2.me/submissions/b626c4c6-0704-4501-a133-62b46dcd335f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) :
    3 * |a| + |a + 3 * b| + |5 * b + c| + 5 * |c| ≥
      (28 / 19) * |a + b + 4 * c| := by
  have ht : |a + b + 4 * c| ≤
      (19 / 28) * (3 * |a| + |a + 3 * b| + |5 * b + c| + 5 * |c|) := by
    apply abs_le.mpr
    constructor <;>
      linarith [le_abs_self a, neg_le_abs a, le_abs_self (a + 3 * b),
        neg_le_abs (a + 3 * b), le_abs_self (5 * b + c), neg_le_abs (5 * b + c),
        le_abs_self c, neg_le_abs c, abs_nonneg a, abs_nonneg (5 * b + c)]
  linarith

#print axioms solution
