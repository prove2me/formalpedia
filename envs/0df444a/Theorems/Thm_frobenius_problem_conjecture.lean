-- Prove2me | Theorems.Thm_frobenius_problem_conjecture
-- name    : frobenius_problem_conjecture
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T02:51:58.37676+00:00
-- url     : https://prove2.me/theorems/e79c31a3-13e0-4626-b442-50eb2cc71359
-- statement:
--   Sylvester-Frobenius theorem: The largest integer not representable as ax+by (with a,b coprime and x,y ≥ 0) is ab-a-b. Proved. For 3 or more coin denominations, the problem of finding the Frobenius number exactly is NP-hard.
-- source:
--   https://en.wikipedia.org/wiki/Coin_problem

import Mathlib

import Mathlib

theorem frobenius_problem_conjecture (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hcop : Nat.Coprime a b) :
    ∀ n : ℕ, a * b - a - b < n →
    ∃ x y : ℕ, n = a * x + b * y := by
  sorry
