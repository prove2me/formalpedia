-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_counting_data_of_maximal_planar_drawing
-- name    : WilliamsonShmoys.exists_triangulated_planar_counting_data_of_maximal_planar_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T00:51:35.900492+00:00
-- url     : https://prove2.me/theorems/463b2b68-5f3b-42b0-a160-4e60ee89475d
-- title:
--   Maximal planar drawings yield triangular-face counting data
-- statement:
--   For a finite graph with at least three vertices, a crossing-free drawing and maximality among planar supergraphs yield a face count satisfying Euler’s identity and the degree sum for triangular faces. This isolates the geometric work needed to show that maximality forces triangular faces.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_TriangulatedPlanarCountingData
set_option autoImplicit false

theorem WilliamsonShmoys.exists_triangulated_planar_counting_data_of_maximal_planar_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V,
      K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L ->
      L <= K) :
    Nonempty (WilliamsonShmoys.TriangulatedPlanarCountingData K) := by sorry
