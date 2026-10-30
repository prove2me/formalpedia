-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_lower_bound_from_drawing
-- name    : WilliamsonShmoys.planar_maximal_edge_lower_bound_from_drawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:43:50.090965+00:00
-- url     : https://prove2.me/theorems/baf59c52-9c88-41d0-8fbc-8b75407a1236
-- title:
--   Edge lower bound for a maximal drawable graph
-- statement:
--   A finite simple graph with at least three vertices that is maximal among drawable supergraphs on the same vertex type has at least 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_edge_lower_bound_from_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
