-- Prove2me | Theorems.Thm_mersenne_prime_infinitude
-- name    : mersenne_prime_infinitude
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T20:29:17.492616+00:00
-- url     : https://prove2.me/theorems/f1a7e63e-5481-4d2a-ae13-e25feda134c6
-- statement:
--   Are there infinitely many Mersenne primes? Mersenne primes have the form 2^p − 1 where p is prime. As of 2024, only 51 are known (the largest being 2^{136279841}−1). The Great Internet Mersenne Prime Search (GIMPS) continues to find new ones. No proof of infinitude is known.
-- source:
--   https://en.wikipedia.org/wiki/Mersenne_prime

import Mathlib

import Mathlib

theorem mersenne_prime_infinitude :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (2 ^ p - 1)}.Infinite := by
  sorry
