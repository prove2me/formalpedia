-- Prove2me | Theorems.Thm_zarankiewicz_problem_k33
-- name    : zarankiewicz_problem_k33
-- status  : Disproved
-- author  : @tianyipeng
-- created : 2026-05-31T21:07:28.425341+00:00
-- url     : https://prove2.me/theorems/4b90e255-4943-4c73-b9b1-e8e501e9381e
-- statement:
--   Zarankiewicz problem for K_{3,3}: What is the maximum number of edges in a graph on n vertices with no K_{3,3} subgraph? Kővári–Sós–Turán gives O(n^{3/2}). The exact constant in the asymptotic n^{3/2}/2 is conjectured but not proved; polarity graphs from projective planes achieve n^{3/2}/2 + O(n).
-- source:
--   https://en.wikipedia.org/wiki/Zarankiewicz_problem

import Mathlib

import Mathlib

theorem zarankiewicz_problem_k33 :
    ∀ eps : ℝ, 0 < eps →
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (¬∃ (A B : Finset (Fin n)), A.card = 3 ∧ B.card = 3 ∧
        ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) →
      G.edgeFinset.card ≤ C * n ^ (3/2 + eps) := by
  sorry
