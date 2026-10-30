-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_3bbe118b_2c52_4e44_a40f_aa9dcfe8d0b0_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_3bbe118b_2c52_4e44_a40f_aa9dcfe8d0b0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:37:25.636118+00:00
-- url     : https://prove2.me/theorems/82506e18-7d6a-422e-80a5-205ab3f947ca
-- title:
--   Edge count of an inclusion maximal drawable graph
-- statement:
--   If a drawable graph with at least three vertices has no proper drawable supergraph on the same vertices, its edge count is 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_3bbe118b_2c52_4e44_a40f_aa9dcfe8d0b0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hDraw : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
