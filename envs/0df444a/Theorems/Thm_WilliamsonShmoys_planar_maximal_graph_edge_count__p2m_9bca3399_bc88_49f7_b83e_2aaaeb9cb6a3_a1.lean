-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_graph_edge_count__p2m_9bca3399_bc88_49f7_b83e_2aaaeb9cb6a3_a1
-- name    : WilliamsonShmoys.planar_maximal_graph_edge_count__p2m_9bca3399_bc88_49f7_b83e_2aaaeb9cb6a3_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:25:31.642206+00:00
-- url     : https://prove2.me/theorems/c8d05df2-843d-4472-95c9-9f82c949001b
-- title:
--   An edge-maximal drawable graph has the planar maximum edge count
-- statement:
--   For at least three vertices, a drawable simple graph that is maximal under drawable edge supergraphs has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_graph_edge_count__p2m_9bca3399_bc88_49f7_b83e_2aaaeb9cb6a3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ (M : SimpleGraph V) [DecidableRel M.Adj],
      HasPlanarDrawingOn M →
      G.edgeFinset ⊆ M.edgeFinset →
      M.edgeFinset ⊆ G.edgeFinset) :
    G.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
