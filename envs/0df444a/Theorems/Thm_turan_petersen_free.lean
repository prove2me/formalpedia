-- Prove2me | Theorems.Thm_turan_petersen_free
-- name    : turan_petersen_free
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T01:56:29.413343+00:00
-- url     : https://prove2.me/theorems/0090e7fc-670a-4ec7-9d56-b3ecc378e1ab
-- statement:
--   Turán-type problem for Petersen-free graphs: Max edges in n-vertex graph with no Petersen subgraph. Turán density π(Petersen) is unknown; conjectured 3/4 by Bondy–Simonovits.
-- source:
--   https://en.wikipedia.org/wiki/Petersen_graph

import Mathlib

import Mathlib

theorem turan_petersen_free :
    ∀ eps : ℝ, 0 < eps →
    ∃ N : ℕ, ∀ (n : ℕ) (_ : N ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      let petersen_edges : Finset (ℕ × ℕ) :=
        {(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
          (5,7),(7,9),(9,6),(6,8),(8,5)}
      (¬∃ (phi : Fin 10 → Fin n), Function.Injective phi ∧
        ∀ i j : Fin 10, (i.val, j.val) ∈ petersen_edges → G.Adj (phi i) (phi j)) →
      (G.edgeFinset.card : ℝ) ≤ (3/4 + eps) * n * (n - 1) / 2 := by
  sorry
