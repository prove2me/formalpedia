-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_triangular_map_face_count
-- name    : WilliamsonShmoys.maximal_planar_drawing_triangular_map_face_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-25T22:54:28.773047+00:00
-- url     : https://prove2.me/theorems/1412e851-c896-4214-8017-3b8f16a45cde
-- title:
--   Face count of the triangular map of a maximal planar drawing
-- statement:
--   For any triangular map on a finite simple graph that has a crossing-free drawing, at least three vertices, and is maximal among graphs with such drawings, the number of faces is `2|V| - 4`. The hypotheses also cover the three-vertex boundary case, where the formula gives two faces. The proof route is Euler’s formula and the maximal planar edge count, followed by counting the map’s darts through its face-corner equivalence.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_drawing_triangular_map_face_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H)
    (m : Nat)
    (M : WilliamsonShmoys.TriangularMap H (Fin m)) :
    2 * Fintype.card V = m + 4 := by sorry
