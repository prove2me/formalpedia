-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation
-- name    : WilliamsonShmoys.planar_drawing_triangulation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T04:27:07.230407+00:00
-- url     : https://prove2.me/theorems/2efd0b1e-9b39-43b2-8b4f-9355cd283e88
-- title:
--   Triangulation extension of a connected planar drawing
-- statement:
--   Every connected finite simple graph with at least three vertices and a crossing-free drawing can be extended, without adding vertices, to a planar simple graph whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hconn : P.Connected)
    (hV : 3 <= Fintype.card V) :
    ∃ Q : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      P.edgeSet ⊆ Q.edgeSet ∧
      Q.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
