-- Prove2me | solution 1 for lean_workbook_plus_18678
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:13:01.92608+00:00
-- url     : https://prove2.me/submissions/0d698fc6-4913-4d58-906b-1a3e76f4f7af

import Mathlib.Analysis.Complex.Basic

theorem solution (a b m n : ℕ) (h₁ : a < b ∧ m < n) (h₂ : a - b = m - n) (h₃ : a + b ≥ m + n) : a / b ≥ m / n := by
  rw [Nat.div_eq_of_lt h₁.1, Nat.div_eq_of_lt h₁.2]
