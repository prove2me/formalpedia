-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_for_triangulated_face_data
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_for_triangulated_face_data
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:37:43.788779+00:00
-- url     : https://prove2.me/theorems/0d6855cc-5062-4808-8487-8440fd9bb7d3
-- title:
--   Maximal planar graphs have the extremal edge count
-- statement:
--   A finite graph with the given crossing-free drawing that is maximal among planar graphs on its vertex type has exactly 3n−6 edges when it has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_for_triangulated_face_data
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K -> H <= K -> K <= H)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
