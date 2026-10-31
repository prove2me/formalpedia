-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_equation__p2m_62a3a1a3_c41c_45ae_9d73_85a6165d1dd4_a1
-- name    : WilliamsonShmoys.planar_drawing_euler_equation__p2m_62a3a1a3_c41c_45ae_9d73_85a6165d1dd4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:21:22.607726+00:00
-- url     : https://prove2.me/theorems/b443656f-128d-4272-bd94-52f4b62f95d7
-- title:
--   Euler equation for a connected planar drawing
-- statement:
--   For a connected graph with at least three vertices and a crossing-free drawing, the number of faces satisfies Euler’s equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_equation__p2m_62a3a1a3_c41c_45ae_9d73_85a6165d1dd4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by sorry
