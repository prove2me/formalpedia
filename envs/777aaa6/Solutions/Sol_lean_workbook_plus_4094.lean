-- Prove2me | solution 1 for lean_workbook_plus_4094
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:24:29.632077+00:00
-- url     : https://prove2.me/submissions/6ad11a97-33b7-4368-ac37-b70dfe7e8288

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) : |x| ≤ 1/2 * x^2 + 1/2 ↔ (|x| - 1)^2 ≥ 0 := by
  constructor
  · intro _
    positivity
  · intro _
    nlinarith [sq_nonneg (|x| - 1), sq_abs x]
