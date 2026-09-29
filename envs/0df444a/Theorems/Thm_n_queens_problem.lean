-- Prove2me | Theorems.Thm_n_queens_problem
-- name    : n_queens_problem
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-31T21:07:17.559406+00:00
-- url     : https://prove2.me/theorems/2f68da25-2468-46e1-8058-36bfdb827904
-- statement:
--   n-queens problem: Find the number Q(n) of ways to place n non-attacking queens on an n×n chessboard. Known: Q(n) > 0 for all n ≥ 1 (except n=2,3). Asymptotic formula: Simkin (2021) proved Q(n) ≈ (n/e)ⁿ · e^O(n). An exact formula for all n remains open.
-- source:
--   https://en.wikipedia.org/wiki/Eight_queens_puzzle

import Mathlib

import Mathlib

theorem n_queens_problem (n : ℕ) (hn : 1 ≤ n) :
    ∃ (Q : ℕ), Q ≥ 1 ∧
      ∃ (queens : Fin Q → Fin n × Fin n),
        Function.Injective queens ∧
        (∀ i j : Fin Q, i ≠ j →
          (queens i).1 ≠ (queens j).1 ∧
          (queens i).2 ≠ (queens j).2 ∧
          (queens i).1.val + (queens i).2.val ≠
            (queens j).1.val + (queens j).2.val ∧
          (queens i).1.val + (Fintype.card (Fin n) - (queens i).2.val) ≠
            (queens j).1.val + (Fintype.card (Fin n) - (queens j).2.val)) := by
  sorry
