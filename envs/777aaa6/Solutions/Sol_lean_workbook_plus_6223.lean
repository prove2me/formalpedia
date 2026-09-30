-- Prove2me | solution 1 for lean_workbook_plus_6223
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:08:49.344149+00:00
-- url     : https://prove2.me/submissions/6cd2273e-017c-419c-8574-7857542f7cdc

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ a b c : ℝ, a ≥ 1 ∧ b ≥ 1 ∧ c ≥ 1 ∧ a + b + c = 5 → a * b * c ≥ 3 := by
  rintro a b c ⟨ha, hb, hc, h⟩
  have ha' : 0 ≤ a - 1 := by linarith
  have hb' : 0 ≤ b - 1 := by linarith
  have hc' : 0 ≤ c - 1 := by linarith
  nlinarith [mul_nonneg (mul_nonneg ha' hb') hc', mul_nonneg ha' hb', mul_nonneg hb' hc', mul_nonneg ha' hc']
