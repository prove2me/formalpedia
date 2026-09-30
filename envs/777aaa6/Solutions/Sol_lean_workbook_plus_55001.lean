-- Prove2me | solution 1 for lean_workbook_plus_55001
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:10:29.888618+00:00
-- url     : https://prove2.me/submissions/e68e4455-5c3f-4a6d-8d85-0eb849096593

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1) : (a / (a + 1) * b + 1) + (b / (b + 1) * c + 1) + (c / (c + 1) * a + 1) ≥ 3 / 4 := by
  obtain ⟨ha, hb, hc, _⟩ := ha
  have h1 : a / (a + 1) * b ≥ 0 := by positivity
  have h2 : b / (b + 1) * c ≥ 0 := by positivity
  have h3 : c / (c + 1) * a ≥ 0 := by positivity
  linarith
