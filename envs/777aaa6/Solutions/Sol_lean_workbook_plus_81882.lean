-- Prove2me | solution 1 for lean_workbook_plus_81882
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:20:41.374742+00:00
-- url     : https://prove2.me/submissions/a38c8a49-4b0a-4860-82ba-5eb61daccef4

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) :
    (4 / 3) * (a ^ 2 + 2 * b ^ 2 + 6 * a * c + 9 * c ^ 2) =
        (4 / 3) * (2 * b ^ 2 + (a + 3 * c) ^ 2) ∧
      (4 / 3) * (2 * b ^ 2 + (a + 3 * c) ^ 2) ≥ 0 := by
  constructor
  · ring
  · positivity

#print axioms solution
