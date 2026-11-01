-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_saturated_planar_graph_edge_lower_bound__p2m_af9692fd_71ca_4e9b_bb88_c2808556729a_a3
-- name    : WilliamsonShmoys.edge_saturated_planar_graph_edge_lower_bound__p2m_af9692fd_71ca_4e9b_bb88_c2808556729a_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:07:24.382008+00:00
-- url     : https://prove2.me/theorems/e079b09e-e4e7-4f37-a7db-f0169ce5ff8c
-- title:
--   Edge lower bound for an edge-saturated drawable graph
-- statement:
--   A finite simple graph on at least three vertices has at least 3|V|−6 edges if it has a crossing-free drawing and no missing edge can occur in any drawable supergraph containing it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.edge_saturated_planar_graph_edge_lower_bound__p2m_af9692fd_71ca_4e9b_bb88_c2808556729a_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hblocked : ∀ u v, u ≠ v → ¬ H.Adj u v →
      ∀ K : SimpleGraph V, H ≤ K → K.Adj u v →
        WilliamsonShmoys.HasPlanarDrawingOn K → False) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
