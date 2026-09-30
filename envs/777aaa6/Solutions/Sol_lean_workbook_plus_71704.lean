-- Prove2me | solution 1 for lean_workbook_plus_71704
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:32:55.730355+00:00
-- url     : https://prove2.me/submissions/8043a932-a858-40b9-824e-611af6aa5d17

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) : (a * (a + 1) + b * (b + 1))^2 ≥ (8:ℝ) / 3 * (a * b * (a * b + 1) + (a + b) * (a^2 + b^2)) := by
  have hpos : 0 ≤ 11 * a ^ 2 + 18 * a * b + 11 * b ^ 2 - 4 * a - 4 * b + 8 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (5 * (a + b) - 1)]
  nlinarith [mul_nonneg (sq_nonneg (a - b)) hpos, sq_nonneg ((a + b) * (a + b - 2))]
