-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count__p2m_b94cb538_0af7_43ff_a8d3_ab44b482c981_a2
-- name    : WilliamsonShmoys.planar_drawing_face_count__p2m_b94cb538_0af7_43ff_a8d3_ab44b482c981_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:22:20.936852+00:00
-- url     : https://prove2.me/theorems/62a3a1a3-c41c-45ae-9d73-85a6165d1dd4
-- title:
--   Euler face count and boundary incidence bound for a connected simple planar drawing
-- statement:
--   There is a natural-number face count satisfying Euler’s equation, and the total face-boundary incidence count is at least three per face and at most twice the number of edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_count__p2m_b94cb538_0af7_43ff_a8d3_ab44b482c981_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by sorry
