-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_triangulation_extension_v2
-- name    : WilliamsonShmoys.maximal_planar_edge_count_triangulation_extension_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T11:30:07.303912+00:00
-- url     : https://prove2.me/theorems/e86e41b9-7012-4cde-8e0d-3df43b92beb5
-- title:
--   Triangulated extension edge count for a planar drawing
-- statement:
--   Every finite graph on at least three vertices with a drawing satisfying `HasPlanarDrawingOn` has a drawable supergraph on the same vertex type whose edge count plus six equals three times the vertex count. The parent applies maximality to identify this supergraph with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_triangulation_extension_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V) :
    exists L : SimpleGraph V,
      K <= L /\ HasPlanarDrawingOn L /\
        L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
