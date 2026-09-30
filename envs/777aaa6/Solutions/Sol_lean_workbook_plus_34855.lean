-- Prove2me | solution 1 for lean_workbook_plus_34855
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:06:58.846539+00:00
-- url     : https://prove2.me/submissions/699c8a31-e219-4723-a059-fcb462b759d6

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) : 1 + x^2 * y^2 + z^2 * x^2 + y^2 * z^2 >= 4 * x * y * z := by
  rcases le_total 0 (x * y) with h | h
  · nlinarith [sq_nonneg (x * y - 1), sq_nonneg (z * (x - y)), mul_nonneg h (sq_nonneg (z - 1))]
  · have h' : 0 ≤ -(x * y) := by linarith
    nlinarith [sq_nonneg (x * y + 1), sq_nonneg (z * (x + y)), mul_nonneg h' (sq_nonneg (z + 1))]
