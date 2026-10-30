-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count_data_from_arcs
-- name    : WilliamsonShmoys.planar_drawing_face_count_data_from_arcs
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:46:41.000978+00:00
-- url     : https://prove2.me/theorems/76e41017-a7fc-4590-92f2-1534df857548
-- title:
--   Euler face count and boundary incidence bound from a planar arc drawing
-- statement:
--   For a connected simple graph on at least three vertices with the supplied crossing-free drawing, some natural face count satisfies Euler’s equation and the lower bound of three edge-side incidences per face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_count_data_from_arcs
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    Exists fun f : Nat =>
      K.edgeSet.ncard + 2 = Fintype.card V + f /\
      3 * f <= 2 * K.edgeSet.ncard := by sorry
