-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_face_count_certificate
-- name    : WilliamsonShmoys.maximal_planar_edge_count_for_face_count_certificate
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T02:46:34.767415+00:00
-- url     : https://prove2.me/theorems/efc6e0da-9220-4b86-92e9-448c3d6e41a4
-- title:
--   Edge count for a maximal graph with a crossing-free arc drawing
-- statement:
--   A simple graph on at least three vertices with a crossing-free arc drawing, maximal among drawable supergraphs on the same vertex type, has exactly 3|V| − 6 edges. This supplies the planar counting result needed to choose the target’s face count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_edge_count_for_face_count_certificate
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ J : SimpleGraph V,
      H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
