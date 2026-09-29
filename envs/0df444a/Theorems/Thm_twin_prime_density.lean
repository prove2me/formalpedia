-- Prove2me | Theorems.Thm_twin_prime_density
-- name    : twin_prime_density
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T13:44:19.26873+00:00
-- url     : https://prove2.me/theorems/44cfba95-1d58-4d45-a766-c7c2ca2f6f3a
-- statement:
--   Hardy-Littlewood twin prime constant: The number of twin primes up to x is ~ C₂ · x/(log x)² where C₂ = 2∏_{p≥3}(p(p-2)/(p-1)²) ≈ 1.3203. Brun proved the sum of reciprocals converges. Hardy-Littlewood conjecture predicts the constant.
-- source:
--   https://en.wikipedia.org/wiki/Twin_prime

import Mathlib

import Mathlib

theorem twin_prime_density :
    ∃ (C : ℝ), 0 < C ∧
    Filter.Tendsto (fun x : ℝ =>
      (∑ p ∈ (Finset.range (Nat.floor x)).filter
        (fun n => Nat.Prime n ∧ Nat.Prime (n + 2)), (1 : ℝ)) /
      (x / (Real.log x) ^ 2))
    Filter.atTop (nhds C) := by
  sorry
