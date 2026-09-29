-- Prove2me | Theorems.Thm_erdos_woods_conjecture
-- name    : erdos_woods_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T20:40:36.012689+00:00
-- url     : https://prove2.me/theorems/172efbba-d728-4fa9-bc06-bdc6b76a4294
-- statement:
--   Erdős–Woods conjecture (1981): There exists k such that if two integers a, b satisfy gcd(a+i, b+i) > 1 for all 0 ≤ i < k, then a = b. Equivalently, any two intervals of k consecutive integers with the same set of prime divisors must be identical. The smallest such k (if it exists) is expected to be 16.
-- source:
--   https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Woods_number

import Mathlib

import Mathlib

theorem erdos_woods_conjecture :
    ∃ k : ℕ, 1 ≤ k ∧
    ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      (∀ i : Fin k, ∀ p : ℕ, Nat.Prime p →
        (p ∣ a + i ↔ p ∣ b + i)) →
      a = b := by
  sorry
