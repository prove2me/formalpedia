-- Prove2me | solution 1 for lean_workbook_plus_32594
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:11:24.880592+00:00
-- url     : https://prove2.me/submissions/8112f94e-c557-4cf6-b329-0d07a307d78f

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) (h₁ : 0 < b ∧ b < a ∧ a ≤ 4) (h₂ : 2 * a * b ≤ 3 * a + 4 * b) : a^2 + b^2 ≤ 25 := by
  obtain ⟨hb, hba, ha4⟩ := h₁
  nlinarith [mul_nonneg (sub_nonneg.mpr ha4) hb.le, mul_nonneg (sub_nonneg.mpr ha4) (sub_nonneg.mpr hba.le),
    sq_nonneg (a - 4), sq_nonneg (b - 3), mul_nonneg (sub_nonneg.mpr ha4) (sub_nonneg.mpr ha4),
    mul_pos hb (sub_pos.mpr hba)]
