-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_counting
-- name    : WilliamsonShmoys.planar_drawing_euler_face_counting
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T11:40:24.130863+00:00
-- url     : https://prove2.me/theorems/938fdd01-6fa5-4c53-962c-9b18198ce159
-- title:
--   Euler face-counting data from a connected planar drawing
-- statement:
--   A connected simple graph on at least three vertices with the given crossing-free drawing has finitely many facial boundary lengths satisfying Euler’s equation, double-counting of edge incidences, and a lower bound of three for each face length.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_euler_face_counting
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ (m : ℕ) (boundaryLength : Fin m → ℕ),
      Fintype.card V + m = K.edgeSet.ncard + 2 ∧
      (∑ f : Fin m, boundaryLength f) = 2 * K.edgeSet.ncard ∧
      ∀ f, 3 <= boundaryLength f := by
  sorry
