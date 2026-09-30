-- Prove2me | solution 1 for lean_workbook_plus_140
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:30:51.206292+00:00
-- url     : https://prove2.me/submissions/0aaad896-701c-490a-a553-cd44c8ba646b

import Mathlib

theorem solution (x y : ℝ) : x ^ 2 + x + y ^ 2 + y + 1 ≥ x * y := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y + 2)]
