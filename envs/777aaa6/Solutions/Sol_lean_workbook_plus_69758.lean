-- Prove2me | solution 1 for lean_workbook_plus_69758
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:14:35.911256+00:00
-- url     : https://prove2.me/submissions/935269ae-df82-46cb-8a02-a64a1256d19b

import Mathlib.Analysis.Complex.Basic

theorem solution  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a * b * c = 1) :
  (a + 1) * (b + 1) * (c + 1) ≥ 8 := by
  obtain ⟨ha, hb, hc⟩ := h₀
  have h1 : (a + 1) ^ 2 ≥ 4 * a := by nlinarith [sq_nonneg (a - 1)]
  have h2 : (b + 1) ^ 2 ≥ 4 * b := by nlinarith [sq_nonneg (b - 1)]
  have h3 : (c + 1) ^ 2 ≥ 4 * c := by nlinarith [sq_nonneg (c - 1)]
  have hpos : 0 < (a + 1) * (b + 1) * (c + 1) := by positivity
  have hsq : ((a + 1) * (b + 1) * (c + 1)) ^ 2 ≥ 64 := by
    have h12 : (a + 1) ^ 2 * (b + 1) ^ 2 ≥ (4 * a) * (4 * b) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    have h123 : (a + 1) ^ 2 * (b + 1) ^ 2 * (c + 1) ^ 2 ≥ (4 * a) * (4 * b) * (4 * c) :=
      mul_le_mul h12 h3 (by positivity) (by positivity)
    calc ((a + 1) * (b + 1) * (c + 1)) ^ 2 = (a + 1) ^ 2 * (b + 1) ^ 2 * (c + 1) ^ 2 := by ring
      _ ≥ (4 * a) * (4 * b) * (4 * c) := h123
      _ = 64 * (a * b * c) := by ring
      _ = 64 := by rw [h₁]; ring
  nlinarith [hsq, hpos]
