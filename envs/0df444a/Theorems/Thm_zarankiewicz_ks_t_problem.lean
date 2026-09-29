-- Prove2me | Theorems.Thm_zarankiewicz_ks_t_problem
-- name    : zarankiewicz_ks_t_problem
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T01:57:40.312961+00:00
-- url     : https://prove2.me/theorems/94ee5214-31be-43fa-b68c-8b0b5492fe14
-- statement:
--   Zarankiewicz problem for K_{s,t}-free graphs: Maximum edges in an n-vertex graph with no complete bipartite subgraph K_{s,t}. Kővári–Sós–Turán gives O(n^{2-1/s}). The exact exponent and constant (achieved by algebraic constructions) are open for most s, t.
-- source:
--   https://en.wikipedia.org/wiki/Zarankiewicz_problem

import Mathlib

import Mathlib

theorem zarankiewicz_ks_t_problem (s t : ℕ) (hs : 2 ≤ s) (ht : 2 ≤ t) :
    ∀ eps : ℝ, 0 < eps →
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (¬∃ (A B : Finset (Fin n)), A.card = s ∧ B.card = t ∧
        ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) →
      G.edgeFinset.card ≤ C * n ^ (2 - 1/s + eps) := by
  sorry
