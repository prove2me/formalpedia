-- Prove2me | Theorems.Thm_strong_goldbach_conjecture
-- name    : strong_goldbach_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T03:27:03.805865+00:00
-- url     : https://prove2.me/theorems/764514cb-c2fe-4804-9651-9cbc5e7fbdf7
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
