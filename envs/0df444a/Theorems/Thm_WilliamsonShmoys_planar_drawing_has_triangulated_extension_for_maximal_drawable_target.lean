-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_extension_for_maximal_drawable_target
-- name    : WilliamsonShmoys.planar_drawing_has_triangulated_extension_for_maximal_drawable_target
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T05:53:20.725285+00:00
-- url     : https://prove2.me/theorems/4c6737e9-5665-42a6-ab73-404e97a2f72b
-- title:
--   Drawable graph extends to triangular sphere-face data
-- statement:
--   Every drawable finite simple graph with at least three vertices is contained, on the same vertex set, in a drawable graph admitting triangular sphere-face data. The condition of at least three vertices is retained, including the three-vertex case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlanarTriangulationEulerData

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_triangulated_extension_for_maximal_drawable_target
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        Nonempty (WilliamsonShmoys.TriangulatedSphereFaceData L) := by sorry
