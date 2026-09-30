-- Prove2me | solution 1 for lean_workbook_plus_26308
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:40:26.042036+00:00
-- url     : https://prove2.me/submissions/4130b176-6cd6-4f31-b5a4-9216137d7508

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℝ) (h₁ : y^2 ≤ x ∧ x ≤ 1) (h₂ : 0 ≤ y ∧ y ≤ 1) : 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1 := by
  obtain ⟨h1, h2⟩ := h₁
  obtain ⟨h3, h4⟩ := h₂
  exact ⟨le_trans (sq_nonneg y) h1, h2, h3, h4⟩
