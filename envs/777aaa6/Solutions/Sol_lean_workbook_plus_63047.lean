-- Prove2me | solution 1 for lean_workbook_plus_63047
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:55:11.512597+00:00
-- url     : https://prove2.me/submissions/241cc42b-4ec7-483d-8e93-94773261ad06

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b : ℝ) : Real.sqrt ((a ^ 2 + (1 - b) ^ 2) / 2) ≥
    (a + (1 - b)) / 2 := by
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg (a - (1 - b))]

#print axioms solution
