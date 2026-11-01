-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_simple_graph_edge_lower_bound__p2m_04b260ca_6bc4_40b7_9582_99be510cc2b0_a3
-- name    : WilliamsonShmoys.maximal_planar_simple_graph_edge_lower_bound__p2m_04b260ca_6bc4_40b7_9582_99be510cc2b0_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:48:02.375555+00:00
-- url     : https://prove2.me/theorems/af9692fd-71ca-4e9b-bb88-c2808556729a
-- title:
--   Lower edge bound for a maximal drawable graph
-- statement:
--   A drawable graph maximal among drawable supergraphs on the same vertex type has at least \(3|V|-6\) edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_simple_graph_edge_lower_bound__p2m_04b260ca_6bc4_40b7_9582_99be510cc2b0_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
