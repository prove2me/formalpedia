-- Prove2me | solution 1 for lean_workbook_plus_54751
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:47:54.61256+00:00
-- url     : https://prove2.me/submissions/75c60f50-a111-4ae7-9ab5-8f77a190bdbe

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c d : ℝ) (h₁ : a + c ≥ b + d) (h₂ : a + b = c + d) : a ≥ d ∧ c ≥ b := by
  constructor <;> linarith
