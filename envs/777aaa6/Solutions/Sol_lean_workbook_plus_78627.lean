-- Prove2me | solution 1 for lean_workbook_plus_78627
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:43:07.156272+00:00
-- url     : https://prove2.me/submissions/370161e3-cacc-48c7-bb40-da832bc1d8ec

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination

theorem solution (a b c d A : ℤ)
    (h₁ : b^2 - a^2 = d^2 - c^2) (h₂ : b^2 - a^2 = A) :
    2 * (a + b) * (c + d) * (a * c + b * d - A) =
      ((a + b) * (c + d) - A)^2 := by
  rw [← h₂]
  linear_combination -(b ^ 2 - a ^ 2) * h₁

#print axioms solution
