-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_triangulation_extension
-- name    : WilliamsonShmoys.maximal_planar_drawing_triangulation_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:12:02.944364+00:00
-- url     : https://prove2.me/theorems/2fec2a0c-361d-4b09-9fa8-61f9d0cca5c8
-- title:
--   Triangulated extension of a connected planar drawing
-- statement:
--   Every connected graph with a crossing-free drawing on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
