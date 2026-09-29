-- Prove2me | Theorems.Thm_strong_goldbach_conjecture
-- name    : strong_goldbach_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T03:27:03.805865+00:00
-- url     : https://prove2.me/theorems/1928f5b6-a848-4bd4-bc68-5db2e4cc9011
-- statement:
--   Goldbach's strong conjecture (1742): Every even integer ≥ 4 is the sum of two primes. Verified for n ≤ 4×10^18. One of the most famous open problems.
-- source:
--   https://en.wikipedia.org/wiki/Goldbach%27s_conjecture

import Mathlib

import Mathlib

theorem strong_goldbach_conjecture :
    ∀ n : ℕ, 4 ≤ n → 2 ∣ n →
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  sorry
