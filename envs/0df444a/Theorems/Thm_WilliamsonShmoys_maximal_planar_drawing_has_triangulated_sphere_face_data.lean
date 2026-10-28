-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangulated_sphere_face_data
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_triangulated_sphere_face_data
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T06:22:41.080979+00:00
-- url     : https://prove2.me/theorems/0ddab995-9fc9-48da-8a21-ef5e5a9b5ac2
-- title:
--   A maximal drawable graph has triangular sphere-face data
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable graphs on the same vertex type admits triangular sphere-face data with every edge incident to two face sides and the stated Euler characteristic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlanarTriangulationEulerData

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_has_triangulated_sphere_face_data
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ H : SimpleGraph V, L ≤ H →
      WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ L) :
    Nonempty (WilliamsonShmoys.TriangulatedSphereFaceData L) := by sorry
