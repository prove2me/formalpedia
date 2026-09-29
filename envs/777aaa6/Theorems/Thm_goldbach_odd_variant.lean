-- Prove2me | Theorems.Thm_goldbach_odd_variant
-- name    : goldbach_odd_variant
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T20:11:41.16616+00:00
-- url     : https://prove2.me/theorems/65b06d33-024a-450b-b238-5228a06ef09b
-- statement:
--   Goldbach's weak conjecture (odd Goldbach conjecture): Every odd integer greater than 5 is the sum of three primes. Proved by Helfgott (2013) for all sufficiently large integers, completing the proof for all odd numbers > 5. This is the fully proved version; the strong (even) Goldbach conjecture remains open.
-- source:
--   https://en.wikipedia.org/wiki/Goldbach%27s_weak_conjecture

import Mathlib

import Mathlib

theorem goldbach_odd_variant :
    ∀ n : ℕ, 7 < n → ¬ 2 ∣ n →
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r := by
  sorry
