-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound_for_face_equations
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_for_face_equations
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T16:11:50.161257+00:00
-- url     : https://prove2.me/theorems/d74ea334-c048-433c-9480-21bc8de1f0ae
-- title:
--   Maximal planar drawing edge lower bound for face equations
-- statement:
--   A drawable graph maximal among drawable supergraphs on the same vertex type, with at least three vertices, has at least `3n - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_for_face_equations
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : forall M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet ->
      WilliamsonShmoys.HasPlanarDrawingOn M ->
      Set.Subset M.edgeSet L.edgeSet)
    (hCard : 3 <= Fintype.card V) :
    3 * Fintype.card V <= L.edgeSet.ncard + 6 := by sorry
