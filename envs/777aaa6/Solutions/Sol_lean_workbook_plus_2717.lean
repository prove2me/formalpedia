-- Prove2me | solution 1 for lean_workbook_plus_2717
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:24:50.747884+00:00
-- url     : https://prove2.me/submissions/3c5f1f73-8d39-41af-aa18-ab6893783780

import Mathlib

theorem solution {a b c : ℝ} :
    (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + a * c) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
