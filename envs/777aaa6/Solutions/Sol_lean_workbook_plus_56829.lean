-- Prove2me | solution 1 for lean_workbook_plus_56829
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:56:13.460706+00:00
-- url     : https://prove2.me/submissions/1a297b30-15f2-488c-b676-f070edbe6f95

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a * b + b * c + c * a + a * b * c ≥ 4) :
  a + b + c ≥ 3 + (b - c)^2 / (b + c + 4) := by
  obtain ⟨ha, hb, hc⟩ := h₀
  have hS : 0 < b * c + b + c := by positivity
  have h2 : 0 < b + c + 4 := by positivity
  have key : 0 ≤ (a + b + c - 3) * (b + c + 4) - (b - c)^2 := by
    have hmul : 0 ≤ ((a + b + c - 3) * (b + c + 4) - (b - c)^2) * (b * c + b + c) := by
      nlinarith [mul_nonneg (sub_nonneg.2 h₁) h2.le, sq_nonneg (2 * b * c + b + c - 4)]
    by_contra hneg
    push_neg at hneg
    nlinarith [mul_neg_of_neg_of_pos hneg hS]
  have hrw : a + b + c - (3 + (b - c)^2 / (b + c + 4))
      = ((a + b + c - 3) * (b + c + 4) - (b - c)^2) / (b + c + 4) := by
    field_simp
    ring
  rw [ge_iff_le, ← sub_nonneg, hrw]
  exact div_nonneg key h2.le
