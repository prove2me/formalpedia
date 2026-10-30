-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition__p2m_2f707832_942f_4ae9_9944_7f0d941152ce_a1
-- name    : WilliamsonShmoys.maximal_planar_face_decomposition__p2m_2f707832_942f_4ae9_9944_7f0d941152ce_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T12:31:08.209578+00:00
-- url     : https://prove2.me/theorems/cc582279-bd81-4049-86d4-e111019c4e0a
-- title:
--   Euler and triangular-face equations for a maximal planar drawing
-- statement:
--   For a finite drawable graph with at least three vertices that has no drawable strict supergraph on the same vertices, there is a natural number of faces satisfying Euler’s equation and the triangular face-edge incidence equation. These equations imply the exact edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_face_decomposition__p2m_2f707832_942f_4ae9_9944_7f0d941152ce_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by sorry
