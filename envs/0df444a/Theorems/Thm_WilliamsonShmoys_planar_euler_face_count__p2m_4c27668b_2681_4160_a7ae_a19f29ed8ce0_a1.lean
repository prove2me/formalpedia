-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_euler_face_count__p2m_4c27668b_2681_4160_a7ae_a19f29ed8ce0_a1
-- name    : WilliamsonShmoys.planar_euler_face_count__p2m_4c27668b_2681_4160_a7ae_a19f29ed8ce0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T09:15:45.612996+00:00
-- url     : https://prove2.me/theorems/d0e3f259-840a-4a52-a9c2-c49923d0da41
-- title:
--   Euler face count and boundary bound for a simple planar drawing
-- statement:
--   For a finite connected simple graph with at least three vertices and a crossing-free plane drawing, there is a natural number f (the number of faces) such that three times the number of faces is at most twice the number of edges, and Euler’s formula holds: vertices plus faces equals edges plus two.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_euler_face_count__p2m_4c27668b_2681_4160_a7ae_a19f29ed8ce0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hConn : K.Connected)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V) :
    ∃ f : ℕ, 3 * f <= 2 * K.edgeSet.ncard ∧
      Fintype.card V + f = K.edgeSet.ncard + 2 := by sorry
