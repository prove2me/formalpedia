-- Prove2me | solution 1 for lean_workbook_plus_40494
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:40:16.399854+00:00
-- url     : https://prove2.me/submissions/cb601595-e423-4d31-b104-5b1536e876d6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℝ) (k : ℕ) (h₁ : 0 < k) (h₂ : ∀ n, 3 * k + 11 ≤ n → |a n - 2| < 1 / 3 * (2 / 3)^k) : ∀ n, 3 * k + 11 ≤ n → |a n - 2| < 1 / 3 * (2 / 3)^k := by
  (intros; simp_all)
