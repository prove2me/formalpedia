-- Prove2me | solution 1 for lean_workbook_plus_15515
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:45:35.606224+00:00
-- url     : https://prove2.me/submissions/0e59ecfc-04ad-4683-b56d-d0f110f77578

import Mathlib.Analysis.Complex.Basic

theorem solution  (a : ℕ → ℝ)
  (n : ℕ)
  (h₀ : (a (n + 1))^2 - 3 * a n * a (n + 1) + 2 * (a n)^2 = 0) :
  a (n + 1) = a n ∨ a (n + 1) = 2 * a n := by
  have h : (a (n + 1) - a n) * (a (n + 1) - 2 * a n) = 0 := by linear_combination h₀
  rcases mul_eq_zero.mp h with h1 | h1
  · left; linarith
  · right; linarith
