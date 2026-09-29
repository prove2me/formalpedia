-- Prove2me | Theorems.Thm_lang_trotter_conjecture
-- name    : lang_trotter_conjecture
-- status  : Disproved
-- author  : @tianyipeng
-- created : 2026-06-01T02:47:34.453732+00:00
-- url     : https://prove2.me/theorems/ee6723ba-15ca-4c75-8556-860431b6e4c3
-- statement:
--   Lang-Trotter conjecture (1976): For a fixed integer a and Weil-bounded sequence τ(p), the number of primes p ≤ x with τ(p) = a grows like C·√x/log x. Proved on average over curves; individual cases open.
-- source:
--   https://en.wikipedia.org/wiki/Lang%E2%80%93Trotter_conjecture

import Mathlib

import Mathlib

theorem lang_trotter_conjecture (a b : ℤ) (hdisc : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
    (tau : ℕ → ℤ) (htau : ∀ p : ℕ, Nat.Prime p → |tau p| ≤ 2 * Nat.sqrt p)
    (target : ℤ) :
    ∃ (C : ℝ), 0 < C ∧
    Filter.Tendsto (fun x : ℝ =>
      (∑ p ∈ (Finset.range (Nat.floor x)).filter Nat.Prime,
        if tau p = target then (1 : ℝ) else 0) /
      (Real.sqrt x / Real.log x))
    Filter.atTop (nhds C) := by
  sorry
