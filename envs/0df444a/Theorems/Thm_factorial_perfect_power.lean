-- Prove2me | Theorems.Thm_factorial_perfect_power
-- name    : factorial_perfect_power
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T02:48:45.750876+00:00
-- url     : https://prove2.me/theorems/509d5cea-4cda-469f-b9b5-323c0a20286b
-- statement:
--   Factorial perfect power conjecture: The only perfect powers that are factorials are 1! = 1, 2! = 2, and possibly 1 = 0! = 1. Brocard's problem asks when n! + 1 = m²; here we ask when n! = m^k. No solutions with k ≥ 2 and n ≥ 3 are known.
-- source:
--   https://en.wikipedia.org/wiki/Factorial

import Mathlib

import Mathlib

theorem factorial_perfect_power :
    {(n, m, k) : ℕ × ℕ × ℕ | 1 ≤ n ∧ 2 ≤ m ∧ 2 ≤ k ∧ n.factorial = m ^ k}.Finite := by
  sorry
