-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_certificate__p2m_3061538d_e777_4f56_997f_0c12065c9e75_a1
-- name    : WilliamsonShmoys.planar_drawing_euler_face_certificate__p2m_3061538d_e777_4f56_997f_0c12065c9e75_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:12:45.583791+00:00
-- url     : https://prove2.me/theorems/abda76d0-f206-4b5c-973f-e20fb605b671
-- title:
--   Euler and face-length certificate for a connected planar drawing
-- statement:
--   For a connected simple graph with at least three vertices and a crossing-free drawing, there is a natural number of faces satisfying Euler’s formula and the lower bound of three on the total face-boundary length.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_face_certificate__p2m_3061538d_e777_4f56_997f_0c12065c9e75_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hcard : 3 <= Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f <= 2 * G.edgeSet.ncard := by sorry
