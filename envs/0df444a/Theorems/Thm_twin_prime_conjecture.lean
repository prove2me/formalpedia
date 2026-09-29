-- Prove2me | Theorems.Thm_twin_prime_conjecture
-- name    : twin_prime_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T18:24:59.105782+00:00
-- url     : https://prove2.me/theorems/185e92b6-5906-49df-9d6f-4d95ee47a58d
-- statement:
--   **Twin Prime Conjecture**: There are infinitely many pairs of prime numbers that differ by 2.
--
--   Examples: $(3,5)$, $(5,7)$, $(11,13)$, $(17,19)$, $(29,31)$, ...
--
--   Zhang (2013) proved infinitely many prime pairs differing by at most 70 million; Maynard and Polymath8 reduced this to 246. The gap of exactly 2 remains open.
-- source:
--   https://en.wikipedia.org/wiki/Twin_prime

import Mathlib

theorem twin_prime_conjecture :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}.Infinite := by
  sorry
