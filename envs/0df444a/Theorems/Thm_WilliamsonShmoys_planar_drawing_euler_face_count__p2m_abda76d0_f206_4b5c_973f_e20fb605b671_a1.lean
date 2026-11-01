-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count__p2m_abda76d0_f206_4b5c_973f_e20fb605b671_a1
-- name    : WilliamsonShmoys.planar_drawing_euler_face_count__p2m_abda76d0_f206_4b5c_973f_e20fb605b671_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:24:14.037732+00:00
-- url     : https://prove2.me/theorems/969d30ae-9419-432b-8a8e-f73a0bdb3493
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   A connected graph with a crossing-free drawing has a natural-number face count satisfying Euler's formula. The vertex lower bound is retained to match the target's boundary conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_face_count__p2m_abda76d0_f206_4b5c_973f_e20fb605b671_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hcard : 3 <= Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by sorry
