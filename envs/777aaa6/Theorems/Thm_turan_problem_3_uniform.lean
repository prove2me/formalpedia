-- Prove2me | Theorems.Thm_turan_problem_3_uniform
-- name    : turan_problem_3_uniform
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T20:59:14.59026+00:00
-- url     : https://prove2.me/theorems/f07e1258-6303-4ffc-b9ef-52d4772c5d65
-- statement:
--   Turán's 3-uniform hypergraph problem (Turán 1941): What is the maximum number of 3-element subsets of {1,...,n} with no 4 vertices spanning 4 edges (K_4^(3))? Turán conjectured the maximum is 2/9·n³/6·(1+o(1)). Known: lower bound 2/9, upper bound 5/9. Exact density unknown.
-- source:
--   https://en.wikipedia.org/wiki/Tur%C3%A1n_problem_for_hypergraphs

import Mathlib

import Mathlib

theorem turan_problem_3_uniform :
    ∀ eps : ℝ, 0 < eps →
    ∃ N : ℕ, ∀ (n : ℕ), N ≤ n →
    ∀ (H : Finset (Finset (Fin n))),
      (∀ e ∈ H, e.card = 3) →
      (¬∃ S : Finset (Fin n), S.card = 4 ∧
        S.powersetCard 3 ⊆ H) →
      (H.card : ℝ) ≤ (5/9 + eps) * Nat.choose n 3 := by
  sorry
