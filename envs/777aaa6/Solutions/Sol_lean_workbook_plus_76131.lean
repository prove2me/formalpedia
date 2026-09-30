-- Prove2me | solution 1 for lean_workbook_plus_76131
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:00:18.838162+00:00
-- url     : https://prove2.me/submissions/5875e4a0-5492-46e1-a5ba-197e5a37141e

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith

theorem solution (a b : ℝ) :
    Real.sqrt (2 * (a ^ 2 + 1) * (b ^ 2 + 1)) ≥ |a * b + a + b - 1| := by
  apply Real.abs_le_sqrt
  nlinarith only [sq_nonneg (a * b - a - b - 1)]
