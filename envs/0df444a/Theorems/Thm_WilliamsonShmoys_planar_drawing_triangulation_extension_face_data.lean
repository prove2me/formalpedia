-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_face_data
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension_face_data
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T14:06:59.482424+00:00
-- url     : https://prove2.me/theorems/a20ea340-80ab-45b7-8ed7-5f048ac57c4a
-- title:
--   Triangulation extension for finite planar drawing face data
-- statement:
--   Every finite simple graph with a drawing satisfying `HasPlanarDrawingOn`, on at least three vertices, has a drawable supergraph on the same vertices with exactly $3|V|-6$ edges. The boundary case of three vertices is attained by extending to a triangle. The proof route is planar augmentation to a triangulation followed by Euler’s formula and face-edge incidence; this is the remaining topological core.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_extension_face_data
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ J : SimpleGraph V, H ≤ J ∧ HasPlanarDrawingOn J ∧
      J.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
