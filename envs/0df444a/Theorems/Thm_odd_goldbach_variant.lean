-- Prove2me | Theorems.Thm_odd_goldbach_variant
-- name    : odd_goldbach_variant
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T02:53:41.056731+00:00
-- url     : https://prove2.me/theorems/a4e4f458-3383-4a6c-a7b1-96fdbecb0a60
-- statement:
--   Goldbach's weak conjecture (proved by Helfgott 2013): Every odd n ≥ 7 is a sum of 3 primes. Here the ordered version (p ≤ q ≤ r) is stated. The proof requires the full machinery of Hardy-Littlewood circle method.
-- source:
--   https://en.wikipedia.org/wiki/Goldbach%27s_weak_conjecture

import Mathlib

import Mathlib

theorem odd_goldbach_variant :
    ∀ n : ℕ, 7 ≤ n → ¬ 2 ∣ n →
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      n = p + q + r ∧ p ≤ q ∧ q ≤ r := by
  sorry
