-- Prove2me | Theorems.Thm_regular_prime_conjecture
-- name    : regular_prime_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T21:10:38.173933+00:00
-- url     : https://prove2.me/theorems/444954b9-7211-4739-bea7-dfe88dea1da4
-- statement:
--   Regular prime conjecture: Are there infinitely many regular primes (primes p not dividing the numerator of any Bernoulli number B₂,...,B_{p-3})? Heuristically ~60.7% of primes are regular, but infinitude is unproved.
-- source:
--   https://en.wikipedia.org/wiki/Regular_prime

import Mathlib

import Mathlib

theorem regular_prime_conjecture :
    {p : ℕ | Nat.Prime p ∧
      ∀ k : Fin ((p - 3) / 2 + 1),
        ¬((p : ℤ) ∣ (bernoulli (2 * (k.val + 1))).num)}.Infinite := by
  sorry
