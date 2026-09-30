-- Prove2me | solution 1 for lean_workbook_plus_71452
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:38:11.738506+00:00
-- url     : https://prove2.me/submissions/a62647fa-77c0-47b4-bc9e-d10494009a0f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (x : ℝ) : x + 3 ≤ Real.sqrt (2 * (x ^ 2 + 10)) := by
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg (x - 3)]

#print axioms solution
