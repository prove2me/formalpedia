-- Prove2me | solution 1 for lean_workbook_plus_25310
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:07:26.329827+00:00
-- url     : https://prove2.me/submissions/ead43064-7b9d-4903-a50d-40b79c5eacb2

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (h₁ : a = 1 + b * Real.sqrt c) (h₂ : Real.sqrt c ∉ Set.range ((↑) : ℚ → ℝ)) : ∃ n : ℕ, ∀ ε : ℝ, ε > 0 → |(a + b * Real.sqrt c)^n - 1| < ε :=
  ⟨0, fun ε hε => by simpa using hε⟩
