-- Prove2me | solution 1 for lean_workbook_plus_81538
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:28:26.469185+00:00
-- url     : https://prove2.me/submissions/6b713ae9-7d67-408e-a753-6b583236002c

import Mathlib

theorem solution (a : ℝ) (ha : 0 ≤ a) : Real.sqrt (a^2 / 4) ≥ Real.sqrt (a - 1) := by
  change Real.sqrt (a - 1) ≤ Real.sqrt (a^2 / 4)
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg (a - 2)]
