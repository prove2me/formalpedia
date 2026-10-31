-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_euler_face_count__p2m_34407b99_d8c1_41e6_9706_2994099c89a5_a1
-- name    : WilliamsonShmoys.planar_euler_face_count__p2m_34407b99_d8c1_41e6_9706_2994099c89a5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:29:51.671645+00:00
-- url     : https://prove2.me/theorems/3e960d88-24fa-4e6d-b367-13e60076bdee
-- title:
--   Euler face count for a connected drawn graph
-- statement:
--   A connected graph with the supplied crossing-free drawing has a natural-number face count satisfying Euler’s formula. The child isolates the Euler characteristic argument from the separate edge-incidence estimate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_euler_face_count__p2m_34407b99_d8c1_41e6_9706_2994099c89a5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by sorry
