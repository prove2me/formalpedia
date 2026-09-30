-- Prove2me | solution 1 for lean_workbook_plus_67748
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:19:06.211774+00:00
-- url     : https://prove2.me/submissions/b3100f49-f102-42d9-b331-a841465c41ef

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

theorem solution (a b c d : ℝ) :
    Real.sqrt ((a ^ 2 + d ^ 2) * (b ^ 2 + c ^ 2)) ≥ a * b + c * d := by
  apply Real.le_sqrt_of_sq_le
  nlinarith only [sq_nonneg (a * c - b * d)]
