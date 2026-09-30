-- Prove2me | solution 1 for lean_workbook_plus_2785
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:30:54.11267+00:00
-- url     : https://prove2.me/submissions/c57c8c7a-8a0b-4947-985a-007e2d77981a

import Mathlib

theorem solution {a b c : ℝ} :
    (a + b + c) ^ 2 * (a * b + b * c + c * a) ≥
      6 * a * b * c * (a + b + c) +
        (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a) := by
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)]
