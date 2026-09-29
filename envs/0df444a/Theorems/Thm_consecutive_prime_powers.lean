-- Prove2me | Theorems.Thm_consecutive_prime_powers
-- name    : consecutive_prime_powers
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T03:41:24.396231+00:00
-- url     : https://prove2.me/theorems/ec833c6e-b1d6-49b8-984c-418980585fa7
-- statement:
--   Consecutive prime powers problem: Determine all solutions to a^m + 1 = b^n with a,b,m,n > 1. Catalan's theorem (proved): only 8+1=9, i.e., 2³+1=3². For a^m - b^n = 1 with m,n ≥ 2 it's Mihailescu.
-- source:
--   https://en.wikipedia.org/wiki/Catalan%27s_conjecture

import Mathlib

import Mathlib

theorem consecutive_prime_powers :
    {(a, b) : ℕ × ℕ | 1 < a ∧ 1 < b ∧
      ∃ m n : ℕ, 2 ≤ m ∧ 2 ≤ n ∧ a ^ m + 1 = b ^ n}.Finite := by
  sorry
