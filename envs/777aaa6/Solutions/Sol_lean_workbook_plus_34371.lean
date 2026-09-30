-- Prove2me | solution 1 for lean_workbook_plus_34371
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:17:28.339466+00:00
-- url     : https://prove2.me/submissions/f2f9e052-e26e-417a-8552-b30d0f986309

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ a b : ℝ,  Real.sqrt (a ^ 2 - a * b + b ^ 2) ≥ (a + b) / 2 ↔ (a - b) ^ 2 ≥ 0 := by
  intro a b
  constructor
  · intro _
    positivity
  · intro _
    exact le_trans (le_abs_self _) (Real.abs_le_sqrt (by nlinarith [sq_nonneg (a - b)]))
