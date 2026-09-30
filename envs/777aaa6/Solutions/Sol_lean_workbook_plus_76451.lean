-- Prove2me | solution 1 for lean_workbook_plus_76451
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:27:04.774571+00:00
-- url     : https://prove2.me/submissions/0a0c0c8b-058c-4108-b9da-4524e794771c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) :
    3 * |a| + |a + 2 * b| + |5 * b + c| + 7 * |c| ≥
      (37 / 24) * |a + b + 5 * c| := by
  rcases le_total 0 (a + b + 5 * c) with ht | ht
  · rw [abs_of_nonneg ht]
    linarith [le_abs_self a, neg_le_abs (a + 2 * b), le_abs_self (5 * b + c), le_abs_self c,
      abs_nonneg a, abs_nonneg (5 * b + c)]
  · rw [abs_of_nonpos ht]
    linarith [neg_le_abs a, le_abs_self (a + 2 * b), neg_le_abs (5 * b + c), neg_le_abs c,
      abs_nonneg a, abs_nonneg (5 * b + c)]
