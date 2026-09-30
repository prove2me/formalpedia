-- Prove2me | solution 1 for lean_workbook_plus_44995
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:10:31.058549+00:00
-- url     : https://prove2.me/submissions/9dd1b03b-e695-4381-b48c-d641d229829d

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) (k : ℕ) (h₁ : n = 6 * k) (h₂ : Nat.gcd k 6 = 1) (h₃ : k > 1) : n < Nat.factorial n := by
  exact Nat.lt_factorial_self (by omega)
