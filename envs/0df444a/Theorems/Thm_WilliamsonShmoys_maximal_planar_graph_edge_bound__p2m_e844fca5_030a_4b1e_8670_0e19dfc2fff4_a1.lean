-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_bound__p2m_e844fca5_030a_4b1e_8670_0e19dfc2fff4_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_e844fca5_030a_4b1e_8670_0e19dfc2fff4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:23:59.935563+00:00
-- url     : https://prove2.me/theorems/90141f6c-e00d-474f-bb06-5b30de1c5624
-- title:
--   Edge bound for an edge-maximal drawable graph
-- statement:
--   An edge-maximal graph with the specified planar drawing and at least three vertices has at most three times its number of vertices minus six edges. Prove this by showing maximality forces a triangulated embedding, then count edges using Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_e844fca5_030a_4b1e_8670_0e19dfc2fff4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K)
    (hn : 3 <= Fintype.card V) :
    (letI : DecidableRel K.Adj := dK;
     K.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
