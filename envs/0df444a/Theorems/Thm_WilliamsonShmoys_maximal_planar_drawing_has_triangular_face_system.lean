-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangular_face_system
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_triangular_face_system
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:02:23.435529+00:00
-- url     : https://prove2.me/theorems/fa41f5ff-de0e-49b5-a2e5-07264cd20226
-- title:
--   A maximal planar drawing has triangular face data
-- statement:
--   A connected graph on at least three vertices with a crossing-free drawing, maximal among planar supergraphs on the same vertex type, admits triangular face data satisfying edge incidence and Euler’s equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_TriangularPlaneFaceSystem

theorem WilliamsonShmoys.maximal_planar_drawing_has_triangular_face_system
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall H' : SimpleGraph V, H < H' ->
      ¬ (WilliamsonShmoys.HasPlanarDrawingOn H')) :
    WilliamsonShmoys.HasTriangularPlaneFaceSystem H := by sorry
