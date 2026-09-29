-- Prove2me | Theorems.Thm_square_sum_two_primes
-- name    : square_sum_two_primes
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T03:41:56.198411+00:00
-- url     : https://prove2.me/theorems/91601106-1121-4762-a0c4-d308fa9949cb
-- statement:
--   Goldbach-like for squares: Is every even perfect square n² > 4 a sum of two primes? Equivalent to: for every n, there exist primes p, q with n² = p+q. Weaker than Goldbach (which covers all even numbers). Open.
-- source:
--   https://en.wikipedia.org/wiki/Goldbach%27s_conjecture

import Mathlib

import Mathlib

theorem square_sum_two_primes :
    {n : ℕ | ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n ^ 2 = p + q}.Infinite := by
  sorry
