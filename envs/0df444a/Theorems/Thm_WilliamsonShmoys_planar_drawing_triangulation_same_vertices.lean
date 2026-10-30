-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_same_vertices
-- name    : WilliamsonShmoys.planar_drawing_triangulation_same_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:54:13.124401+00:00
-- url     : https://prove2.me/theorems/058cf02c-49dc-459f-ad8c-a90bc75334c7
-- title:
--   Triangulate a connected planar drawing on the same vertices
-- statement:
--   Every connected simple graph on at least three vertices with a crossing-free drawing has a crossing-free supergraph on the same vertices with exactly 3|V|−6 edges, and the original edge count is no larger.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_same_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
