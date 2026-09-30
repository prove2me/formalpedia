-- Prove2me | solution 1 for lean_workbook_plus_24066
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:16:47.716047+00:00
-- url     : https://prove2.me/submissions/0030146f-9888-4cb3-be63-d6e689926d95

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) : (x * y + y * z + x * z - 1) ^ 2 ≤ (1 + x ^ 2) * (1 + y ^ 2) * (1 + z ^ 2) := by
  nlinarith [sq_nonneg (x + y + z - x * y * z)]
