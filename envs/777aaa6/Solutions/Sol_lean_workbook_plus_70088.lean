-- Prove2me | solution 1 for lean_workbook_plus_70088
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:59:48.464718+00:00
-- url     : https://prove2.me/submissions/973d9bf1-f291-48d8-9866-2cb6f5507a26

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c d : ℝ) (h : a + b + c + d ≥
    2 * Real.sqrt ((a + b) * (c + d))) :
    (a + b) * (c + d) ≤ (a + b + c + d) ^ 2 / 4 := by
  nlinarith [sq_nonneg (a + b - (c + d))]

#print axioms solution
