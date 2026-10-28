-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_via_triangulation_1f8dbaa1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_via_triangulation_1f8dbaa1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T09:41:46.107085+00:00
-- url     : https://prove2.me/theorems/e62410f4-830b-45c4-bd7d-6df7f03cb790
-- title:
--   Maximality yields the triangulation lower bound
-- statement:
--   A drawable graph on at least three vertices with no drawable supergraph on the same vertex type has at least `3|V| - 6` edges. Extend the drawing to a triangulation on the same vertices; maximality identifies the extension with the original graph, and Euler’s formula gives the count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_via_triangulation_1f8dbaa1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall J : SimpleGraph V,
      H <= J -> WilliamsonShmoys.HasPlanarDrawingOn J -> J = H) :
    3 * Fintype.card V <= H.edgeSet.ncard + 6 := by sorry
