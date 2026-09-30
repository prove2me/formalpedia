-- Prove2me | solution 1 for lean_workbook_plus_50879
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:24:24.064081+00:00
-- url     : https://prove2.me/submissions/a1b0d289-0d54-4c01-b8df-d6cc87b48f2b

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ x y : ℝ, 2 * x * y ≤ (2 * x + y) ^ 2 / 2 := by
  intro x y
  nlinarith [sq_nonneg x, sq_nonneg y]
