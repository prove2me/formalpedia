-- Prove2me | Theorems.Thm_odd_perfect_number_conjecture
-- name    : odd_perfect_number_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T18:25:57.778815+00:00
-- url     : https://prove2.me/theorems/63ec2311-71fe-46e4-b7aa-4049907e8dad
-- statement:
--   **Odd Perfect Number Conjecture**: No odd perfect number exists; every perfect number is even.
--
--   A perfect number equals the sum of its proper divisors: $6 = 1+2+3$, $28 = 1+2+4+7+14$, ...
--
--   All known perfect numbers are even of the form $2^{p-1}(2^p-1)$ where $2^p-1$ is Mersenne prime (Euler). Any odd perfect number must exceed $10^{1500}$ and have at least 101 prime factors. Open since antiquity.
-- source:
--   https://en.wikipedia.org/wiki/Perfect_number

import Mathlib

theorem odd_perfect_number_conjecture (n : ℕ) (hn : Nat.Perfect n) : Even n := by
  sorry
