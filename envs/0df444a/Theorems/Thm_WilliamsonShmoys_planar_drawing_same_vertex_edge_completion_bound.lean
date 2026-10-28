-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_same_vertex_edge_completion_bound
-- name    : WilliamsonShmoys.planar_drawing_same_vertex_edge_completion_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T23:14:41.8739+00:00
-- url     : https://prove2.me/theorems/8bedde10-aeef-4d86-9712-46fdb1742194
-- title:
--   Edge completion bound for a finite planar drawing
-- statement:
--   A finite simple graph with at least three vertices and a crossing-free drawing has a same-vertex-set supergraph whose edge count is exactly 3n − 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_same_vertex_edge_completion_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
