-- Prove2me | Theorems.Thm_goldbach
-- name    : goldbach
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T18:24:48.708081+00:00
-- url     : https://prove2.me/theorems/bb6d08eb-9860-4a58-8ee3-b9b366f83dca
-- statement:
--   **Goldbach's Conjecture**: Every even integer greater than 2 can be expressed as the sum of two prime numbers.
--
--   For example: $4 = 2 + 2$, $6 = 3 + 3$, $8 = 3 + 5$, $100 = 3 + 97$.
--
--   First stated by Christian Goldbach in a 1742 letter to Leonhard Euler. Verified computationally up to $4 \times 10^{18}$ but unproved in general. The weak Goldbach conjecture (every odd $n > 5$ is sum of three primes) was proved by Helfgott in 2013.
-- source:
--   https://en.wikipedia.org/wiki/Goldbach%27s_conjecture

import Mathlib

theorem goldbach :
    ∀ n : ℕ, 2 < n → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  sorry
