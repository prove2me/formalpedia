-- Prove2me | solution 1 for lean_workbook_plus_36019
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:40:07.961067+00:00
-- url     : https://prove2.me/submissions/0a23fe8c-9e9c-4aa6-9519-847a67cc6e38

import Mathlib.Analysis.Complex.Basic

theorem solution (a b k : ℝ) (ha : 0 < a) (hb : 0 < b) (hk : 0 ≤ k ∧ k ≤ 32) : 1 / a + 1 / b + k / (a + b) ≥ 3 * (1 + k / 4) * (1 / (2 * a + b) + 1 / (2 * b + a)) := by
  obtain ⟨hk0, hk32⟩ := hk
  rw [ge_iff_le, ← sub_nonneg]
  have hab : 0 < a + b := by linarith
  have h1 : 0 < 2 * a + b := by linarith
  have h2 : 0 < 2 * b + a := by linarith
  have key : 1 / a + 1 / b + k / (a + b) - 3 * (1 + k / 4) * (1 / (2 * a + b) + 1 / (2 * b + a))
      = (a - b) ^ 2 * (8 * (a + b) ^ 2 - k * (a * b)) / (4 * (a * b * (a + b) * (2 * a + b) * (2 * b + a))) := by
    field_simp
    ring
  rw [key]
  apply div_nonneg
  · apply mul_nonneg (sq_nonneg _)
    nlinarith [sq_nonneg (a - b), mul_nonneg (mul_pos ha hb).le (by linarith : 0 ≤ 32 - k)]
  · positivity
