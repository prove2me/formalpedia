-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_supergraph_triangulation
-- name    : WilliamsonShmoys.planar_drawable_supergraph_triangulation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T18:00:15.357267+00:00
-- url     : https://prove2.me/theorems/2a27a388-e06b-4db0-bfe8-7a93ec4c9c7f
-- title:
--   Triangulated drawable supergraph on the same vertices
-- statement:
--   Any graph with a crossing-free drawing on a finite ordered vertex type of size at least three has a drawable supergraph on the same vertices whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawable_supergraph_triangulation
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
