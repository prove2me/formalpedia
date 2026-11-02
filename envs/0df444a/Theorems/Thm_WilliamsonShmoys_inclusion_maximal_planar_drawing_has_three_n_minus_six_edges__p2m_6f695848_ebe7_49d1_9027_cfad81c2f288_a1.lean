-- Prove2me | Theorems.Thm_WilliamsonShmoys_inclusion_maximal_planar_drawing_has_three_n_minus_six_edges__p2m_6f695848_ebe7_49d1_9027_cfad81c2f288_a1
-- name    : WilliamsonShmoys.inclusion_maximal_planar_drawing_has_three_n_minus_six_edges__p2m_6f695848_ebe7_49d1_9027_cfad81c2f288_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:55:33.788485+00:00
-- url     : https://prove2.me/theorems/b7da0b5c-b8e2-42e5-8f2d-d77c61d3fb07
-- title:
--   An inclusion-maximal planar drawing has 3n−6 edges
-- statement:
--   An inclusion-maximal graph admitting the specified crossing-free drawing, on at least three vertices, has exactly 3n−6 edges. The proof must establish that maximality triangulates the faces, then formalize the Euler and face-degree equations for the supplied drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.inclusion_maximal_planar_drawing_has_three_n_minus_six_edges__p2m_6f695848_ebe7_49d1_9027_cfad81c2f288_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hmax : ∀ Q : SimpleGraph V, P ≤ Q → WilliamsonShmoys.HasPlanarDrawingOn Q → Q = P)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel P.Adj := Classical.decRel P.Adj
    3 * Fintype.card V = P.edgeFinset.card + 6 := by sorry
