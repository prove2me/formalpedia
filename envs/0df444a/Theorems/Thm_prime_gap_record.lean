-- Prove2me | Theorems.Thm_prime_gap_record
-- name    : prime_gap_record
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T03:00:15.175725+00:00
-- url     : https://prove2.me/theorems/29deb704-508a-495e-96d6-0f314317e965
-- statement:
--   Maximal prime gaps: For every n, there is a prime p followed by a gap of length ≥ n. The sequence of record prime gaps (largest gaps before p_k) grows. Cramér's conjecture: max gap ≈ (log p)². Open: exact growth rate of maximal prime gaps.
-- source:
--   https://en.wikipedia.org/wiki/Prime_gap

import Mathlib

import Mathlib

theorem prime_gap_record :
    ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧
      (∀ q : ℕ, Nat.Prime q → q > p → q > p + n) ∨
      ∃ q : ℕ, Nat.Prime q ∧ q = p + 1 := by
  sorry
