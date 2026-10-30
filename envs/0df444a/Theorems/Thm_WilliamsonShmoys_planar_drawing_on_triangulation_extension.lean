-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_on_triangulation_extension
-- name    : WilliamsonShmoys.planar_drawing_on_triangulation_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T21:04:10.144993+00:00
-- url     : https://prove2.me/theorems/be6af594-1880-43cc-90a6-94f1106e4a30
-- title:
--   Extend a planar drawing to a triangulation on the same vertices
-- statement:
--   Every graph with a drawing satisfying the supplied planar-drawing predicate on at least three finite ordered vertices is contained in a graph on the same vertices with such a drawing and exactly three times the vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_on_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧
      HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
