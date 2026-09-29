-- Prove2me | solution 1 for lean_workbook_plus_80127
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:00:28.643292+00:00
-- url     : https://prove2.me/submissions/014bc0d7-6319-449c-a03f-b8d6e60078da

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (a : ℕ → ℝ) (n : ℕ) (h₀ : a n ≥ 1) (h₁ : ∀ x ≥ 1, f x ≤ a n * (x + 1)) : ∀ x ≥ 1, f x ≤ a n * (x + 1) := by
  (intros; simp_all)
