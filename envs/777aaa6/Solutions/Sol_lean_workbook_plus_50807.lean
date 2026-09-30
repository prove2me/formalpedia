-- Prove2me | solution 1 for lean_workbook_plus_50807
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:42:19.7665+00:00
-- url     : https://prove2.me/submissions/59422c17-272e-42e6-98b1-0ef9c029df2e

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) : 5 * x ^ 4 + x ^ 2 + 2 ≥ 5 * x := by
  nlinarith [sq_nonneg (x^2 - 1/3), sq_nonneg (x - 15/26)]
