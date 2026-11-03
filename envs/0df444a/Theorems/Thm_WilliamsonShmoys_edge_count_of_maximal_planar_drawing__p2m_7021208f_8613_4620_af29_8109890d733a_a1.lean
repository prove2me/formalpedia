-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing__p2m_7021208f_8613_4620_af29_8109890d733a_a1
-- name    : WilliamsonShmoys.edge_count_of_maximal_planar_drawing__p2m_7021208f_8613_4620_af29_8109890d733a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:56:32.990792+00:00
-- url     : https://prove2.me/theorems/6e927d54-05a0-4e04-9e4a-5cbec6b81d96
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.edge_count_of_maximal_planar_drawing__p2m_7021208f_8613_4620_af29_8109890d733a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) :
    letI : DecidableRel T.Adj := Classical.decRel T.Adj
    T.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
