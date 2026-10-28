-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_7607aed3
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension_7607aed3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T05:39:44.759384+00:00
-- url     : https://prove2.me/theorems/d831e8b1-4ff6-4efe-84fe-ca840f7a69e4
-- title:
--   Triangulation extension of a connected planar drawing
-- statement:
--   Extend a connected finite simple graph with a crossing-free drawing and at least three vertices to a drawable supergraph on the same vertex set with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_extension_7607aed3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
