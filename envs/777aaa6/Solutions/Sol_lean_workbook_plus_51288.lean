-- Prove2me | solution 1 for lean_workbook_plus_51288
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:40:25.13719+00:00
-- url     : https://prove2.me/submissions/8dc07389-745b-4cb9-a3a8-ad56bb1c2721

import Mathlib.Analysis.Complex.Basic

theorem solution (t : ℝ) (h₁ : t ≥ 2) : (t - 2) * (t + 1) * (8 * t - 7) ≥ 0 := by
  apply mul_nonneg
  · apply mul_nonneg <;> linarith
  · linarith
