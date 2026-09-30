-- Prove2me | solution 1 for lean_workbook_plus_2619
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:30:43.950768+00:00
-- url     : https://prove2.me/submissions/48f912e1-ec57-4363-aff1-cfed59039660

import Mathlib

theorem solution (x : ℝ) : x ^ 2 * abs (x - 1) ≤ x ^ 4 + x ^ 2 + 1 := by
  rcases le_total 0 (x - 1) with hx | hx
  · rw [abs_of_nonneg hx]
    nlinarith [sq_nonneg (x ^ 2 - x / 2), sq_nonneg x]
  · rw [abs_of_nonpos hx]
    nlinarith [sq_nonneg (x ^ 2 + x / 2 - 1 / 2), sq_nonneg (x + 1 / 3)]
