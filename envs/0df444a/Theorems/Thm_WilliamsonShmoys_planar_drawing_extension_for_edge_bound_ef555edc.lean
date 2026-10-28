-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_for_edge_bound_ef555edc
-- name    : WilliamsonShmoys.planar_drawing_extension_for_edge_bound_ef555edc
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T01:21:06.922496+00:00
-- url     : https://prove2.me/theorems/782e9f5c-d658-4462-b0db-5fd32e317705
-- title:
--   Extend a finite planar drawing to a triangulation on the same vertices
-- statement:
--   Any finite graph with the specified crossing-free drawing and at least three vertices is contained in a graph on the same vertex set with such a drawing and exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_extension_for_edge_bound_ef555edc
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
