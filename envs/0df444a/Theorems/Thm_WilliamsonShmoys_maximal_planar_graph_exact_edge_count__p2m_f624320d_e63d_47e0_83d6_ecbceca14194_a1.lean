-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_exact_edge_count__p2m_f624320d_e63d_47e0_83d6_ecbceca14194_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_exact_edge_count__p2m_f624320d_e63d_47e0_83d6_ecbceca14194_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:40:47.152811+00:00
-- url     : https://prove2.me/theorems/c3a9b232-8896-4daf-b121-720ec89c3bee
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph on the same vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_graph_exact_edge_count__p2m_f624320d_e63d_47e0_83d6_ecbceca14194_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hMaximal : ∀ K : SimpleGraph V,
      N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ N)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
