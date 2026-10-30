-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation_edge_count_completion
-- name    : WilliamsonShmoys.planar_drawing_has_triangulation_edge_count_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T01:16:43.796621+00:00
-- url     : https://prove2.me/theorems/a5cfb50b-4787-4b2f-b9a1-91f61d01226d
-- title:
--   A drawable graph extends to a triangulation edge count
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices is contained in a drawable graph on the same vertices with exactly 3|V| − 6 edges. For three vertices, the completion is the triangle; for larger sets, triangulate a maximal planar extension and count its edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_triangulation_edge_count_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
