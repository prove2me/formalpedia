-- Prove2me | Theorems.Thm_WilliamsonShmoys_simple_planar_face_count_bounds__p2m_bff95f57_b2f4_4a78_b638_ad03e6867777_a2
-- name    : WilliamsonShmoys.simple_planar_face_count_bounds__p2m_bff95f57_b2f4_4a78_b638_ad03e6867777_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:14:35.729626+00:00
-- url     : https://prove2.me/theorems/34407b99-d8c1-41e6-9706-2994099c89a5
-- title:
--   Euler face count and boundary incidence for a simple planar graph
-- statement:
--   For a connected simple graph on at least three vertices with the supplied crossing-free drawing, there is a number of faces satisfying Euler's equation, and the sum of facial boundary lengths is at least three per face and equals twice the number of edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.simple_planar_face_count_bounds__p2m_bff95f57_b2f4_4a78_b638_ad03e6867777_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by sorry
