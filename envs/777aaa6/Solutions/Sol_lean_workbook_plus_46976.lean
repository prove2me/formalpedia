-- Prove2me | solution 1 for lean_workbook_plus_46976
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:17:55.10419+00:00
-- url     : https://prove2.me/submissions/7ed03fb6-d554-4011-9480-c0dc794ba4ac

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c: ℝ) (h1 : a >= 1 ∧ b >= 1 ∧ c >= 1): a + b + c >= 3 := by
  obtain ⟨ha, hb, hc⟩ := h1
  linarith
