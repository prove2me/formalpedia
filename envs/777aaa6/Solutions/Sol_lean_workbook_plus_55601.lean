-- Prove2me | solution 1 for lean_workbook_plus_55601
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:25:02.690024+00:00
-- url     : https://prove2.me/submissions/c5eb5182-86b1-47a5-8658-2a773999b20d

import Mathlib.Analysis.Complex.Basic

theorem solution (b : ℕ → ℝ) (h₁ : ∃ a, ∀ n, |b n| < a) : ∃ a, a ∈ {a : ℝ | ∃ n, b n ∈ Set.Icc a (a + 1)} := by
  exact ⟨b 0, 0, le_refl _, by linarith⟩
