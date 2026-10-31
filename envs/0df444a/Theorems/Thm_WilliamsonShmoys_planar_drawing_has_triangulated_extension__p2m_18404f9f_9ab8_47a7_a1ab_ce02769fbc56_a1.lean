-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_extension__p2m_18404f9f_9ab8_47a7_a1ab_ce02769fbc56_a1
-- name    : WilliamsonShmoys.planar_drawing_has_triangulated_extension__p2m_18404f9f_9ab8_47a7_a1ab_ce02769fbc56_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:20:47.654063+00:00
-- url     : https://prove2.me/theorems/7e28d180-08cc-4953-8752-6b4f2973fe5d
-- title:
--   Planar drawing extends to a triangulated planar graph
-- statement:
--   For every graph with the specified crossing-free drawing and at least three vertices, there is a planar simple supergraph on the same vertex type whose edge count is exactly 3n−6, and the original edge count is at most that count. This is the triangulation-extension step; the vertex-count condition preserves the n=3 boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_triangulated_extension__p2m_18404f9f_9ab8_47a7_a1ab_ce02769fbc56_a1 {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (hDraw : HasPlanarDrawingOn Q)
    (hV : 3 <= Fintype.card V) :
    exists R : SimpleGraph V,
      Q <= R /\ HasPlanarDrawingOn R /\
      Q.edgeSet.ncard <= R.edgeSet.ncard /\
      R.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
