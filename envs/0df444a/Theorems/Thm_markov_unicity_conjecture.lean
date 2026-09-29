-- Prove2me | Theorems.Thm_markov_unicity_conjecture
-- name    : markov_unicity_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T02:15:21.734754+00:00
-- url     : https://prove2.me/theorems/a2d40550-9108-4cf8-9221-ef2db2a957c7
-- statement:
--   Markov unicity conjecture: Each positive integer appears as the largest element in at most one Markov triple (x,y,z) with x²+y²+z²=3xyz. Proved for primes and prime powers; open in general.
-- source:
--   https://en.wikipedia.org/wiki/Markov_number

import Mathlib

import Mathlib

theorem markov_unicity_conjecture :
    ∀ m : ℕ, 1 ≤ m →
    (∃ x y : ℕ, x ^ 2 + y ^ 2 + m ^ 2 = 3 * x * y * m) →
    ∃! p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ p.1 ≤ p.2 ∧ p.2 ≤ m ∧
      p.1 ^ 2 + p.2 ^ 2 + m ^ 2 = 3 * p.1 * p.2 * m := by
  sorry
