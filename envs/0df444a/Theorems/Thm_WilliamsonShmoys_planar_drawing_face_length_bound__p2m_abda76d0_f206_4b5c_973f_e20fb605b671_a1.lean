-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_length_bound__p2m_abda76d0_f206_4b5c_973f_e20fb605b671_a1
-- name    : WilliamsonShmoys.planar_drawing_face_length_bound__p2m_abda76d0_f206_4b5c_973f_e20fb605b671_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:24:17.712969+00:00
-- url     : https://prove2.me/theorems/fdf6b599-6bc6-49f9-8e7c-aa4a3539064a
-- title:
--   Face-incidence bound for a simple planar drawing
-- statement:
--   For a connected simple graph with at least three vertices and a crossing-free drawing, any natural face count satisfying Euler's equation obeys the face-incidence inequality. A proof route is to represent each face by its boundary walk, show each such walk has length at least three, and count two incidences per edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_face_length_bound__p2m_abda76d0_f206_4b5c_973f_e20fb605b671_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hcard : 3 <= Fintype.card V)
    (f : ℕ)
    (hEuler : Fintype.card V + f = G.edgeSet.ncard + 2) :
    3 * f <= 2 * G.edgeSet.ncard := by sorry
