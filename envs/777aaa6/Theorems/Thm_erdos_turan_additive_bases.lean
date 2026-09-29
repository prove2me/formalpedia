-- Prove2me | Theorems.Thm_erdos_turan_additive_bases
-- name    : erdos_turan_additive_bases
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T02:11:39.78359+00:00
-- url     : https://prove2.me/theorems/9691d098-158c-4790-b864-95e33694e72a
-- statement:
--   Erdős–Turán conjecture on additive bases (1941): If A is an additive basis of order 2 for the natural numbers (every sufficiently large integer is a+b with a,b ∈ A), then the number of representations r(n) = #{(a,b): a+b=n} is unbounded. Related to Goldbach and the distribution of primes.
-- source:
--   https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Tur%C3%A1n_conjecture_on_additive_bases

import Mathlib

import Mathlib

theorem erdos_turan_additive_bases :
    ∀ (A : Set ℕ),
      (∃ C : ℕ, ∀ n : ℕ, {(a, b) : ℕ × ℕ | a ∈ A ∧ b ∈ A ∧ a + b = n}.ncard ≤ C) →
      ¬ (∀ n : ℕ, ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ a + b = n) := by
  sorry
