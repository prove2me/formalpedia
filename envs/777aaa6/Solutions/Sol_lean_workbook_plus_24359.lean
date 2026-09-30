-- Prove2me | solution 1 for lean_workbook_plus_24359
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:21:01.411247+00:00
-- url     : https://prove2.me/submissions/0a053ce6-3fd3-46c0-90f6-53ff60a37a53

import Mathlib.Analysis.Complex.Basic

theorem solution (a : ℝ) (ha : 0 < a) : ∃ x, x^2 ∈ Set.Icc (a^2) ((a + 1)^2) := by
  exact ⟨a, le_refl _, by nlinarith⟩
