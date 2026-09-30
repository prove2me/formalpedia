-- Prove2me | solution 2 for lean_workbook_plus_21470
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:45:59.245336+00:00
-- url     : https://prove2.me/submissions/8a167336-b871-408b-be57-65c92e9ba413

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (f : ℝ → ℝ) (h1 : ∀ x, f x ≠ 0) (h2 : ∀ x, x ≠ 0) : (∀ ε > 0, ∃ N : ℕ, ∀ x > N, |f x - (a * x + b)| < ε) → ∀ ε > 0, ∃ N : ℕ, ∀ x > N, |f x / x - a| < ε := by
  (intros; simp_all)
