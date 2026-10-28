-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_maximal_edge_saturation
-- name    : WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_maximal_edge_saturation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T10:42:43.805753+00:00
-- url     : https://prove2.me/theorems/fa75ef82-40e9-4805-b383-09708e069c33
-- title:
--   Maximal planar edge saturation
-- statement:
--   A graph maximal among drawable supergraphs on the same vertex type, with at least three vertices, has at least 3n − 6 edges. A proof route is to extend the drawing to a triangulation by adding edges, then apply maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_maximal_edge_saturation
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hDraw : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
