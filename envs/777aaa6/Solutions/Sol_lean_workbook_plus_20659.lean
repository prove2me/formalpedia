-- Prove2me | solution 1 for lean_workbook_plus_20659
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:02:42.616719+00:00
-- url     : https://prove2.me/submissions/3beca3a1-c3bc-44b5-8796-8b392f2e5b36

import Mathlib.Analysis.Complex.Basic

theorem solution {a b c : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a ≥ b) (hbc : b ≥ c) (hca : c ≥ a) : a^3 + b^3 + c^3 + 6 * a * b * c ≤ 2 * (a * b * (a + b) + b * c * (b + c) + c * a * (c + a)) := by
  have hba : b = a := le_antisymm hab (le_trans hca hbc)
  have hcb : c = a := le_antisymm (le_trans hbc hab) hca
  subst hba hcb
  nlinarith [pow_nonneg ha 3, mul_nonneg (mul_nonneg ha ha) ha]
