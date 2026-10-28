-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_has_triangulated_sphere_face_data
-- name    : WilliamsonShmoys.maximal_planar_has_triangulated_sphere_face_data
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T07:55:38.621987+00:00
-- url     : https://prove2.me/theorems/1076637a-f3c8-431b-b9fb-12cc46dba807
-- title:
--   A maximal planar drawing yields triangular sphere face data
-- statement:
--   A drawable graph on at least three vertices that has no proper drawable supergraph admits triangular sphere-face data, including two incidences per edge and Euler characteristic 2.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlanarTriangulationEulerData

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_has_triangulated_sphere_face_data
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    Nonempty (WilliamsonShmoys.TriangulatedSphereFaceData H) := by sorry
