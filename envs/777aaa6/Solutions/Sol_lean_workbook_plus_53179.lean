-- Prove2me | solution 1 for lean_workbook_plus_53179
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:39:34.903334+00:00
-- url     : https://prove2.me/submissions/83f625c4-7bc0-47bb-a3ed-ea7c25b9abc6

import Mathlib.Analysis.Complex.Basic

theorem solution (m n : ℕ) (h₁ : Nat.gcd m 2*n = 1) (h₂ : ∃ k : ℕ, m^4 - 2*n^4 = k^2) : ∃ x y : ℕ, Nat.gcd x 2*y = 1 ∧ ∃ k : ℕ, x^4 - 2*y^4 = k^2 :=
  ⟨1, 1, by decide, 0, by decide⟩
