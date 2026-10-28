-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_on_same_vertices
-- name    : WilliamsonShmoys.planar_drawing_triangulation_completion_on_same_vertices
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:57:18.942009+00:00
-- url     : https://prove2.me/theorems/e0661f22-04f1-4138-9730-6c8dde1880cf
-- title:
--   Triangulation completion on the same vertex set
-- statement:
--   Every finite graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn has a planar supergraph on the same vertices whose edge count is exactly three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_completion_on_same_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
