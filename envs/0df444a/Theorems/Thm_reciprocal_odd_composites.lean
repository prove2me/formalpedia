-- Prove2me | Theorems.Thm_reciprocal_odd_composites
-- name    : reciprocal_odd_composites
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T02:48:34.855605+00:00
-- url     : https://prove2.me/theorems/5d284bf4-5f87-4dbd-8c34-3fbe54ab31e6
-- statement:
--   Reciprocals of odd composites: The sum ∑ 1/(odd composite) = 1/9 + 1/15 + 1/21 + ... converges (since ∑ 1/(n log n) diverges but we exclude primes). The exact value of this sum is unknown.
-- source:
--   https://en.wikipedia.org/wiki/List_of_sums_of_reciprocals

import Mathlib

import Mathlib

theorem reciprocal_odd_composites :
    ∃ (S : ℝ), S = ∑' n : {n : ℕ // ¬ Nat.Prime n ∧ ¬ 2 ∣ n ∧ 3 ≤ n},
      (1 : ℝ) / n := by
  sorry
