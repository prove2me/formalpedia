-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_lower_bound_bd88397e_retry3
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound_bd88397e_retry3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T19:59:35.984008+00:00
-- url     : https://prove2.me/theorems/fe39cb94-f82e-4553-8662-9097c26d5d3d
-- title:
--   Maximal drawable graph edge-count lower bound
-- statement:
--   A drawable graph maximal among drawable supergraphs on the same vertex set has at least 3|V|−6 edges. This isolates the step showing that maximality forces a triangulation, including the three-vertex case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound_bd88397e_retry3
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet ⊆ L.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
