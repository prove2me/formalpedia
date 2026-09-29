-- Prove2me | Theorems.Thm_infinitely_many_mersenne_primes
-- name    : infinitely_many_mersenne_primes
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T18:30:56.267697+00:00
-- url     : https://prove2.me/theorems/538d1096-f6ef-4227-bcfb-84ffacf4b932
-- statement:
--   **Mersenne Prime Conjecture**: There are infinitely many Mersenne primes, i.e., primes of the form $2^k - 1$.
--
--   Known Mersenne primes: $k = 2, 3, 5, 7, 13, 17, 19, 31, 61, 89, \ldots$ (51 known as of 2024). The largest known prime is always a Mersenne prime (currently $2^{136279841} - 1$, found by GIMPS in 2024).
--
--   Necessary condition: $k$ must itself be prime. But not all prime $k$ give Mersenne primes (e.g., $2^{11} - 1 = 2047 = 23 \times 89$). The Lenstra–Pomerance–Wagstaff conjecture gives a heuristic count of $\sim e^\gamma \log_2 \log_2 x$ Mersenne primes $\leq 2^x$.
-- source:
--   https://en.wikipedia.org/wiki/Mersenne_prime

import Mathlib

theorem infinitely_many_mersenne_primes :
    {k : ℕ | Nat.Prime (2 ^ k - 1)}.Infinite := by
  sorry
