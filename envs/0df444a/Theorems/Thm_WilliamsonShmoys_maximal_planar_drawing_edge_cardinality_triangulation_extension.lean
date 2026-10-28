-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_cardinality_triangulation_extension
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_cardinality_triangulation_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T06:36:35.781348+00:00
-- url     : https://prove2.me/theorems/efc9e89c-ebbd-41d7-941f-3b13c7de33da
-- title:
--   Planar drawings extend to a triangulation with exact edge count
-- statement:
--   Every finite planar drawing on at least three vertices can be extended, on the same vertex type, to a planar graph with exactly three times the vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_cardinality_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
