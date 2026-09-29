-- Prove2me | Theorems.Thm_primes_in_short_intervals
-- name    : primes_in_short_intervals
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T21:07:06.222653+00:00
-- url     : https://prove2.me/theorems/7c323f3e-404e-45a7-8423-632329ed2223
-- statement:
--   Primes in short intervals: Is there always a prime between x and x + x^{1/2+ε} for large x and any ε > 0? Follows from RH which gives primes up to O(x^{1/2} log x). Known unconditionally: Huxley (1972) gives prime in [x, x + x^{7/12}]. The exponent 1/2 is the RH prediction.
-- source:
--   https://en.wikipedia.org/wiki/Prime_gap

import Mathlib

import Mathlib

theorem primes_in_short_intervals :
    ∀ eps : ℝ, 0 < eps →
    ∃ N : ℕ, ∀ (x : ℝ), N ≤ x →
      ∃ p : ℕ, Nat.Prime p ∧ (x : ℝ) < p ∧ p ≤ x + x ^ (1/2 + eps) := by
  sorry
