-- Prove2me | Theorems.Thm_non_wieferich_prime_conjecture
-- name    : non_wieferich_prime_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T19:38:51.650648+00:00
-- url     : https://prove2.me/theorems/24b9cba0-1848-4a7e-bea4-1a41d9e0a71d
-- statement:
--   Wieferich prime conjecture: There are infinitely many non-Wieferich primes (primes p where p² does not divide 2^(p−1)−1). Only two Wieferich primes are known: 1093 and 3511.
-- source:
--   https://en.wikipedia.org/wiki/Wieferich_prime

import Mathlib

import Mathlib

theorem non_wieferich_prime_conjecture :
    {p : ℕ | Nat.Prime p ∧ ¬((p : ℤ)^2 ∣ 2^(p - 1) - 1)}.Infinite := by
  sorry
