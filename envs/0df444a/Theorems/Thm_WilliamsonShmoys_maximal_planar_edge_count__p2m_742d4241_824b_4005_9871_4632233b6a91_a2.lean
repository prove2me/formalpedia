-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_742d4241_824b_4005_9871_4632233b6a91_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_742d4241_824b_4005_9871_4632233b6a91_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T13:04:33.78344+00:00
-- url     : https://prove2.me/theorems/b2020b19-fb40-461e-a788-a72b44070de7
-- title:
--   Edge count of a maximal drawable planar graph
-- statement:
--   For a drawable finite simple graph on at least three vertices, if no strict supergraph on the same vertex type is drawable, then its edge count plus six equals three times its number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_742d4241_824b_4005_9871_4632233b6a91_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
