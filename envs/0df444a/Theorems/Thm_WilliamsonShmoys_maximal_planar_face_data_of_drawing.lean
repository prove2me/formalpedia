-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_data_of_drawing
-- name    : WilliamsonShmoys.maximal_planar_face_data_of_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T13:07:24.769975+00:00
-- url     : https://prove2.me/theorems/08b15342-231e-43dd-a6bd-2aaaa0cbdffb
-- title:
--   Construct face data for a maximal planar drawing
-- statement:
--   A crossing-free drawing of an inclusion-maximal planar simple graph on at least three vertices admits finite face and edge data satisfying Euler’s equation, three incident edges per face, two incident faces per edge, and equality of the data’s edge count with the graph’s edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_TriangulatedPlanarFaceData

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_data_of_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K → H ≤ K → K ≤ H)
    (hV : 3 ≤ Fintype.card V) :
    Nonempty (WilliamsonShmoys.TriangulatedPlanarFaceData H) := by sorry
