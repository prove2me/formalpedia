-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_face_certificate__p2m_3003f6fd_5536_41b8_8ede_329302ccc292_a3
-- name    : WilliamsonShmoys.maximal_drawing_face_certificate__p2m_3003f6fd_5536_41b8_8ede_329302ccc292_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T02:05:19.122+00:00
-- url     : https://prove2.me/theorems/68d7f981-8fd3-430a-af01-9cf213d6ade1
-- title:
--   Euler and face-incidence certificate for a maximal drawing
-- statement:
--   A drawable graph that is maximal under edge inclusion on at least three vertices has a face count satisfying Euler's identity and the face-incidence inequality needed for the edge lower bound. The proof must build the face structure from the continuous arc drawing and show maximality forces triangular faces.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawing_face_certificate__p2m_3003f6fd_5536_41b8_8ede_329302ccc292_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ L : SimpleGraph V,
      G.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet ⊆ G.edgeSet)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : Nat,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      2 * G.edgeSet.ncard ≤ 3 * f := by sorry
