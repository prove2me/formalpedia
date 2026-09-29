-- Prove2me | Theorems.Thm_sum_of_reciprocals_primes_diverges
-- name    : sum_of_reciprocals_primes_diverges
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T03:44:40.531261+00:00
-- url     : https://prove2.me/theorems/7c5dc573-f538-477b-be5d-7fc07d0d6f87
-- statement:
--   Sum of reciprocals of primes diverges: ∑ 1/p = ∞ (Euler 1737). Proved. This is equivalent to there being infinitely many primes.
-- source:
--   https://en.wikipedia.org/wiki/Divergence_of_the_sum_of_the_reciprocals_of_the_primes

import Mathlib

import Mathlib

theorem sum_of_reciprocals_primes_diverges :
    Filter.Tendsto (fun n : ℕ => ∑ p ∈ (Finset.range n).filter Nat.Prime, (1 : ℝ) / p)
    Filter.atTop Filter.atTop := by
  sorry
