-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count_certificate
-- name    : WilliamsonShmoys.planar_drawing_face_count_certificate
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T09:39:05.604639+00:00
-- url     : https://prove2.me/theorems/113e29a6-207c-4745-85d3-0c1876af3a03
-- title:
--   Face-count data for a connected planar drawing
-- statement:
--   Extract the aggregate face count and total facial boundary incidences from the drawing. Euler’s equation gives the first equality, every edge contributes two incidences (including bridges), and the total number of incidences is at least three times the face count. The connectedness and at-least-three-vertices hypotheses must be used to exclude degenerate facial boundary walks.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_face_count_certificate
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) (hCard : 3 ≤ Fintype.card V) :
    ∃ f b : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      b = 2 * K.edgeSet.ncard ∧
      3 * f ≤ b := by sorry
