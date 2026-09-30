-- Prove2me | solution 1 for lean_workbook_plus_4742
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:40:29.111891+00:00
-- url     : https://prove2.me/submissions/9e30b72f-c492-4cca-8199-91d41616d10a

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) : a * b + b * c + c * a ≤ (a + b + c) ^ 2 / 3 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
