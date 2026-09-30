-- Prove2me | solution 1 for lean_workbook_plus_2460
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:30:54.819805+00:00
-- url     : https://prove2.me/submissions/5e48c5b8-4d85-44a2-9e66-f66d1ce7c3ca

import Mathlib

theorem solution (a b c d : ℝ) :
    (a ^ 2 * b + c ^ 2 * d) * (b + d) ≥ b * d * (a + c) ^ 2 := by
  nlinarith [sq_nonneg (a * b - c * d)]
