-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition__p2m_ac618f5b_f1ff_4053_9ae3_bb0fc54b8c70_a1
-- name    : WilliamsonShmoys.maximal_planar_face_decomposition__p2m_ac618f5b_f1ff_4053_9ae3_bb0fc54b8c70_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:07:50.211599+00:00
-- url     : https://prove2.me/theorems/ea40f167-79e5-4439-8a7d-ae09e117fb58
-- title:
--   Euler and triangular-face equations for a maximal planar drawing
-- statement:
--   A drawable graph on at least three vertices that has no drawable strict supergraph on the same vertex type has a face count satisfying Euler’s equation and the triangular face-edge incidence equation. These equations imply that its edge count is 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_face_decomposition__p2m_ac618f5b_f1ff_4053_9ae3_bb0fc54b8c70_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by sorry
