-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count__p2m_e9cc7ebe_a4b1_46c5_abf0_9e9356d8afb2_a1
-- name    : WilliamsonShmoys.planar_drawing_euler_face_count__p2m_e9cc7ebe_a4b1_46c5_abf0_9e9356d8afb2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:52:42.749984+00:00
-- url     : https://prove2.me/theorems/37f8e29f-bb54-4230-8529-b67f7e327c0e
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   A connected finite graph with a crossing-free drawing has a natural-number face count satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_face_count__p2m_e9cc7ebe_a4b1_46c5_abf0_9e9356d8afb2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by sorry
