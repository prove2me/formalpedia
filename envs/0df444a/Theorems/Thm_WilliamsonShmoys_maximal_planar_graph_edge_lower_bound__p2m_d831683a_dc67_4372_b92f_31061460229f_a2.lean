-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_lower_bound__p2m_d831683a_dc67_4372_b92f_31061460229f_a2
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_d831683a_dc67_4372_b92f_31061460229f_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T00:55:51.690011+00:00
-- url     : https://prove2.me/theorems/605ea55b-898a-485b-a8cc-847d4f0e84e6
-- title:
--   Edge lower bound for maximal drawable graphs
-- statement:
--   An inclusion-maximal graph admitting a crossing-free drawing on a finite ordered vertex type with at least three vertices has at least 3n−6 edges. Maximality ranges over every drawable supergraph on the same vertex type; the lower bound includes the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_d831683a_dc67_4372_b92f_31061460229f_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn N → M ≤ N → N = M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by sorry
