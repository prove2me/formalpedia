-- Prove2me | Theorems.Thm_pinwheel_conjecture
-- name    : pinwheel_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T02:17:05.075695+00:00
-- url     : https://prove2.me/theorems/d2de569e-90c2-4bdc-a81c-8a5becfc7a6e
-- statement:
--   Pinwheel conjecture: If the sum of reciprocals of positive integers a₁,...,aₖ is ≤ 5/6, then there is a valid pinwheel schedule (periodic schedule where task i appears every aᵢ periods). Proved for sum ≤ 1/2 and special cases; threshold 5/6 is open.
-- source:
--   https://en.wikipedia.org/wiki/Pinwheel_scheduling

import Mathlib

import Mathlib

theorem pinwheel_conjecture (k : ℕ) (hk : 1 ≤ k)
    (rates : Fin k → ℕ) (hrates : ∀ i, 1 ≤ rates i)
    (hsum : ∑ i, (1 : ℚ) / rates i ≤ 5/6) :
    ∃ (schedule : ℕ → Fin k),
      ∀ i : Fin k, ∀ n : ℕ,
        ∃ m : ℕ, n ≤ m ∧ m < n + rates i ∧ schedule m = i := by
  sorry
